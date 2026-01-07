package main

import (
	"bufio"
	"bytes"
	"crypto/aes"
	"crypto/cipher"
	"crypto/hmac"
	"crypto/rand"
	"crypto/sha256"
	"encoding/csv"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"image"
	_ "image/gif"
	_ "image/jpeg"
	_ "image/png"
	"io/fs"
	"io/ioutil"
	"math"
	"math/rand"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"runtime"
	"sort"
	"strconv"
	"strings"
	"syscall"
	"time"

	"github.com/pelletier/go-toml/v2"
	"golang.org/x/crypto/scrypt"
	"gopkg.in/yaml.v3"
)

const (
	appDirName         = ".myutil"
	clipHistoryName    = "clip_history.json"
	vaultFileName      = "vault.enc"
	vaultSaltName      = "vault.salt"
	clipHistoryMax     = 500
	overwritePasses    = 3
	defaultPreviewLines = 40
)

type ClipEntry struct {
	Time    time.Time `json:"time"`
	Content string    `json:"content"`
	Source  string    `json:"source,omitempty"`
}

type VaultEntry struct {
	Name     string `json:"name"`
	Username string `json:"username,omitempty"`
	Password string `json:"password"`
	Note     string `json:"note,omitempty"`
}

type Vault struct {
	Entries []VaultEntry `json:"entries"`
}

func main() {
	rand.Seed(time.Now().UnixNano())
	if len(os.Args) < 2 {
		printHelp()
		return
	}
	cmd := os.Args[1]
	ensureAppDir()

	switch cmd {
	case "help", "--help", "-h":
		printHelp()
	case "system":
		systemInfo()
	case "cleanup":
		cleanupCmd(os.Args[2:])
	case "copy":
		copyCmd(os.Args[2:])
	case "paste":
		pasteCmd(os.Args[2:])
	case "clip-list":
		clipListCmd(os.Args[2:])
	case "shred":
		shredCmd(os.Args[2:])
	case "preview":
		previewCmd(os.Args[2:])
	case "regex":
		regexCmd(os.Args[2:])
	case "cmdhist":
		cmdHistCmd(os.Args[2:])
	case "convert":
		convertCmd(os.Args[2:])
	case "passgen":
		passGenCmd(os.Args[2:])
	case "passvault":
		passVaultCmd(os.Args[2:])
	case "gitignore":
		gitignoreCmd(os.Args[2:])
	default:
		fmt.Printf("unknown command %q\n\n", cmd)
		printHelp()
	}
}

func printHelp() {
	fmt.Println("myutil — single-file utility")
	fmt.Println()
	fmt.Println("Usage: myutil <command> [args]")
	fmt.Println()
	fmt.Println("Commands:")
	fmt.Println("  system                  Show system info (OS, CPU, memory, disk)")
	fmt.Println("  cleanup [--dry-run] [--days N]  Clean temp files older than N days (default 7).")
	fmt.Println("  copy                    Copy stdin or argument to clipboard and save to history.")
	fmt.Println("  paste                   Print clipboard contents and save to history.")
	fmt.Println("  clip-list               List clipboard history and snippets.")
	fmt.Println("  shred <file> [passes]   Securely overwrite and delete a file (passes default 3).")
	fmt.Println("  preview <file>          Preview text/markdown or print image metadata.")
	fmt.Println("  regex                  Interactive regex tester (see myutil regex --help)")
	fmt.Println("  cmdhist [--shell bash|zsh|powershell] --n N  Show command history and optionally rerun via --run idx")
	fmt.Println("  convert <sub>           Convert between CSV/JSON/YAML/TOML (see subcommands).")
	fmt.Println("  passgen [--len N] [--no-symbols]  Generate password + entropy estimate.")
	fmt.Println("  passvault <sub>         Manage encrypted vault (create/add/get/list/delete).")
	fmt.Println("  gitignore <lang>        Output a .gitignore template for language/project.")
	fmt.Println()
	fmt.Println("See 'myutil <command> --help' for command-specific options.")
}

// -------------------- helper paths --------------------

func ensureAppDir() string {
	home, _ := os.UserHomeDir()
	dir := filepath.Join(home, appDirName)
	os.MkdirAll(dir, 0700)
	return dir
}

func appPath(name string) string {
	return filepath.Join(ensureAppDir(), name)
}

// -------------------- system info --------------------

func systemInfo() {
	fmt.Println("System info:")
	fmt.Printf("  OS: %s\n", runtime.GOOS)
	fmt.Printf("  ARCH: %s\n", runtime.GOARCH)
	hostname, _ := os.Hostname()
	fmt.Printf("  Hostname: %s\n", hostname)
	fmt.Printf("  CPUs: %d\n", runtime.NumCPU())

	// Memory: try unix /proc/meminfo, fallback to syscalls
	if runtime.GOOS == "linux" {
		if data, err := ioutil.ReadFile("/proc/meminfo"); err == nil {
			lines := strings.Split(string(data), "\n")
			for _, l := range lines {
				if strings.HasPrefix(l, "MemTotal:") || strings.HasPrefix(l, "MemFree:") || strings.HasPrefix(l, "MemAvailable:") {
					fmt.Printf("  %s\n", strings.TrimSpace(l))
				}
			}
		}
	}

	// disk usage: root fs
	var stat syscall.Statfs_t
	wd := "/"
	if runtime.GOOS == "windows" {
		wd = os.Getenv("SystemDrive") + "\\"
	}
	err := syscall.Statfs(wd, &stat)
	if err == nil {
		total := stat.Blocks * uint64(stat.Bsize)
		free := stat.Bavail * uint64(stat.Bsize)
		used := total - free
		fmt.Printf("  Disk (%s) total: %s used: %s free: %s\n", wd, bsize(total), bsize(used), bsize(free))
	} else {
		fmt.Printf("  Disk: could not statfs: %v\n", err)
	}
}

// bytes to human
func bsize(b uint64) string {
	const unit = 1024
	if b < unit {
		return fmt.Sprintf("%d B", b)
	}
	div, exp := uint64(unit), 0
	for n := b / unit; n >= unit; n /= unit {
		div *= unit
		exp++
	}
	return fmt.Sprintf("%.1f %cB", float64(b)/float64(div), "KMGTPE"[exp])
}

// -------------------- cleanup --------------------

func cleanupCmd(args []string) {
	fs := flag.NewFlagSet("cleanup", flag.ExitOnError)
	days := fs.Int("days", 7, "delete files older than DAYS")
	dry := fs.Bool("dry-run", false, "do not delete, only show")
	fs.Parse(args)

	tmp := os.TempDir()
	fmt.Printf("Cleaning temp dir %s (older than %d days)\n", tmp, *days)
	threshold := time.Now().Add(-time.Duration(*days) * 24 * time.Hour)
	count := 0
	var total uint64
	filepath.Walk(tmp, func(path string, info fs.FileInfo, err error) error {
		if err != nil {
			return nil
		}
		if info.ModTime().Before(threshold) {
			fmt.Printf("  %s (%d bytes) mod: %s\n", path, info.Size(), info.ModTime().Format(time.RFC3339))
			count++
			total += uint64(info.Size())
			if !*dry {
				// attempt remove: if directory, try remove all
				if info.IsDir() {
					os.RemoveAll(path)
				} else {
					os.Remove(path)
				}
			}
		}
		return nil
	})
	fmt.Printf("Found %d items, total size %s. dry-run=%v\n", count, bsize(total), *dry)
}

// -------------------- clipboard copy/paste + history --------------------

func copyCmd(args []string) {
	fs := flag.NewFlagSet("copy", flag.ExitOnError)
	source := fs.String("s", "", "copy this string instead of stdin")
	fs.Parse(args)

	var data string
	if *source != "" {
		data = *source
	} else {
		info, _ := os.Stdin.Stat()
		if (info.Mode() & os.ModeCharDevice) == 0 {
			// piped input
			buf, _ := ioutil.ReadAll(os.Stdin)
			data = string(buf)
		} else {
			fmt.Println("Enter text to copy (end with EOF / Ctrl-D):")
			buf, _ := ioutil.ReadAll(os.Stdin)
			data = string(buf)
		}
	}
	data = strings.TrimRight(data, "\n")
	if err := clipboardCopy(data); err != nil {
		fmt.Printf("copy failed: %v\n", err)
		fmt.Println("Falling back to showing text. You can copy manually:")
		fmt.Println(data)
	} else {
		fmt.Println("Copied to clipboard.")
	}
	saveClipHistory(data, "copy")
}

func pasteCmd(args []string) {
	fs := flag.NewFlagSet("paste", flag.ExitOnError)
	fs.Parse(args)
	text, err := clipboardPaste()
	if err != nil {
		fmt.Printf("paste failed: %v\n", err)
		return
	}
	fmt.Print(text)
	saveClipHistory(text, "paste")
}

func clipListCmd(args []string) {
	fs := flag.NewFlagSet("clip-list", flag.ExitOnError)
	fs.Parse(args)
	h := loadClipHistory()
	if len(h) == 0 {
		fmt.Println("No clipboard history.")
		return
	}
	for i := len(h) - 1; i >= 0; i-- {
		ci := h[i]
		fmt.Printf("[%d] %s — %s\n", len(h)-i, ci.Time.Format(time.RFC3339), previewLine(ci.Content, 80))
	}
	fmt.Println("\nTo copy an item back to clipboard run: myutil copy -s \"<text>\"")
}

func previewLine(s string, n int) string {
	if len(s) <= n {
		return s
	}
	return s[:n] + "..."
}

func saveClipHistory(data, source string) {
	path := appPath(clipHistoryName)
	h := loadClipHistory()
	entry := ClipEntry{
		Time:    time.Now(),
		Content: data,
		Source:  source,
	}
	h = append(h, entry)
	// trim
	if len(h) > clipHistoryMax {
		h = h[len(h)-clipHistoryMax:]
	}
	b, _ := json.MarshalIndent(h, "", "  ")
	ioutil.WriteFile(path, b, 0600)
}

func loadClipHistory() []ClipEntry {
	path := appPath(clipHistoryName)
	b, err := ioutil.ReadFile(path)
	if err != nil {
		return nil
	}
	var h []ClipEntry
	_ = json.Unmarshal(b, &h)
	return h
}

// clipboard implementations using cli tools
func clipboardCopy(s string) error {
	switch runtime.GOOS {
	case "darwin":
		cmd := exec.Command("pbcopy")
		cmd.Stdin = strings.NewReader(s)
		return cmd.Run()
	case "linux":
		// try wl-copy (wayland) or xclip or xsel
		if _, err := exec.LookPath("wl-copy"); err == nil {
			cmd := exec.Command("wl-copy")
			cmd.Stdin = strings.NewReader(s)
			return cmd.Run()
		}
		if _, err := exec.LookPath("xclip"); err == nil {
			cmd := exec.Command("xclip", "-selection", "clipboard")
			cmd.Stdin = strings.NewReader(s)
			return cmd.Run()
		}
		if _, err := exec.LookPath("xsel"); err == nil {
			cmd := exec.Command("xsel", "--clipboard", "--input")
			cmd.Stdin = strings.NewReader(s)
			return cmd.Run()
		}
		return errors.New("no clipboard tool found (install wl-clipboard, xclip or xsel)")
	case "windows":
		// use clip
		cmd := exec.Command("cmd", "/c", "clip")
		cmd.Stdin = strings.NewReader(s)
		return cmd.Run()
	default:
		return errors.New("unsupported OS clipboard")
	}
}

func clipboardPaste() (string, error) {
	switch runtime.GOOS {
	case "darwin":
		out, err := exec.Command("pbpaste").Output()
		return string(out), err
	case "linux":
		if _, err := exec.LookPath("wl-paste"); err == nil {
			out, err := exec.Command("wl-paste").Output()
			return string(out), err
		}
		if _, err := exec.LookPath("xclip"); err == nil {
			out, err := exec.Command("xclip", "-selection", "clipboard", "-o").Output()
			return string(out), err
		}
		if _, err := exec.LookPath("xsel"); err == nil {
			out, err := exec.Command("xsel", "--clipboard", "--output").Output()
			return string(out), err
		}
		// try reading from primary selection as last resort
		return "", errors.New("no clipboard tool found (install wl-clipboard, xclip or xsel)")
	case "windows":
		out, err := exec.Command("powershell", "-noprofile", "-command", "Get-Clipboard -Raw").Output()
		return string(out), err
	default:
		return "", errors.New("unsupported OS clipboard")
	}
}

// -------------------- shred (secure delete) --------------------

func shredCmd(args []string) {
	fs := flag.NewFlagSet("shred", flag.ExitOnError)
	force := fs.Bool("f", false, "force without prompt")
	fs.Parse(args)
	if fs.NArg() < 1 {
		fmt.Println("usage: myutil shred <file> [passes]")
		return
	}
	path := fs.Arg(0)
	passes := overwritePasses
	if fs.NArg() >= 2 {
		if n, err := strconv.Atoi(fs.Arg(1)); err == nil && n > 0 {
			passes = n
		}
	}
	if !*force {
		fmt.Printf("Are you sure you want to securely delete %s (passes %d)? Type YES: ", path, passes)
		var resp string
		fmt.Scanln(&resp)
		if resp != "YES" {
			fmt.Println("aborted")
			return
		}
	}
	err := secureDelete(path, passes)
	if err != nil {
		fmt.Printf("shred error: %v\n", err)
	} else {
		fmt.Println("file securely deleted.")
	}
}

func secureDelete(path string, passes int) error {
	info, err := os.Stat(path)
	if err != nil {
		return err
	}
	if info.IsDir() {
		// recursively shred files then remove dir
		err := filepath.Walk(path, func(p string, fi fs.FileInfo, err error) error {
			if err != nil {
				return nil
			}
			if fi.IsDir() {
				return nil
			}
			_ = secureDelete(p, passes)
			return nil
		})
		if err != nil {
			return err
		}
		return os.RemoveAll(path)
	}
	f, err := os.OpenFile(path, os.O_WRONLY, 0)
	if err != nil {
		return err
	}
	defer f.Close()
	size := info.Size()
	buf := make([]byte, 4096)
	for pass := 0; pass < passes; pass++ {
		// reset
		f.Seek(0, 0)
		remain := size
		for remain > 0 {
			n := int64(len(buf))
			if remain < n {
				n = remain
			}
			// fill with random
			_, _ = rand.Read(buf[:n])
			_, err := f.Write(buf[:n])
			if err != nil {
				return err
			}
			remain -= n
		}
		f.Sync()
	}
	f.Close()
	// truncate to small random size then remove
	_ = os.Truncate(path, int64(rand.Intn(256)))
	return os.Remove(path)
}

// -------------------- preview --------------------

func previewCmd(args []string) {
	fs := flag.NewFlagSet("preview", flag.ExitOnError)
	lines := fs.Int("n", defaultPreviewLines, "number of lines to show for text")
	fs.Parse(args)
	if fs.NArg() < 1 {
		fmt.Println("usage: myutil preview <file>")
		return
	}
	path := fs.Arg(0)
	info, err := os.Stat(path)
	if err != nil {
		fmt.Printf("stat error: %v\n", err)
		return
	}
	if info.IsDir() {
		fmt.Println("directory - listing:")
		entries, _ := ioutil.ReadDir(path)
		for _, e := range entries {
			fmt.Println(" ", e.Name())
		}
		return
	}
	f, err := os.Open(path)
	if err != nil {
		fmt.Printf("open error: %v\n", err)
		return
	}
	defer f.Close()
	// try detect image
	cfg, format, err := image.DecodeConfig(f)
	if err == nil {
		fmt.Printf("Image: format=%s width=%d height=%d\n", format, cfg.Width, cfg.Height)
		return
	}
	// else treat as text. reopen
	f.Seek(0, 0)
	scanner := bufio.NewScanner(f)
	c := 0
	for scanner.Scan() && c < *lines {
		fmt.Println(scanner.Text())
		c++
	}
}

// -------------------- regex builder & test runner --------------------

func regexCmd(args []string) {
	fs := flag.NewFlagSet("regex", flag.ExitOnError)
	test := fs.String("test", "", "test string (or use stdin)")
	ignore := fs.Bool("i", false, "case-insensitive")
	fs.Parse(args)

	if *test == "" {
		// interactive
		reader := bufio.NewReader(os.Stdin)
		fmt.Println("Interactive regex tester. Type /quit to exit.")
		for {
			fmt.Print("pattern> ")
			pat, _ := reader.ReadString('\n')
			pat = strings.TrimSpace(pat)
			if pat == "" {
				continue
			}
			if pat == "/quit" {
				return
			}
			flags := ""
			if *ignore {
				flags = "(?i)"
			}
			re, err := regexp.Compile(flags + pat)
			if err != nil {
				fmt.Printf("compile error: %v\n", err)
				continue
			}
			fmt.Print("test> ")
			txt, _ := reader.ReadString('\n')
			txt = strings.TrimRight(txt, "\n")
			if re.MatchString(txt) {
				fmt.Println("MATCH")
				fmt.Println("Matches:")
				for i, name := range re.SubexpNames() {
					_ = i
					if name != "" {
						fmt.Println(" named:", name)
					}
				}
				matches := re.FindAllStringSubmatchIndex(txt, -1)
				for _, m := range matches {
					fmt.Println(" -", txt[m[0]:m[1]])
				}
			} else {
				fmt.Println("NO MATCH")
			}
		}
	} else {
		flags := ""
		if *ignore {
			flags = "(?i)"
		}
		reader := bufio.NewReader(os.Stdin)
		fmt.Print("Enter pattern: ")
		patRaw, _ := reader.ReadString('\n')
		pat := strings.TrimSpace(patRaw)
		re, err := regexp.Compile(flags + pat)
		if err != nil {
			fmt.Printf("compile error: %v\n", err)
			return
		}
		if *test != "" {
			if re.MatchString(*test) {
				fmt.Println("MATCH")
				fmt.Println(re.FindStringSubmatch(*test))
			} else {
				fmt.Println("NO MATCH")
			}
		}
	}
}

// -------------------- command history visualizer + rerun --------------------

func cmdHistCmd(args []string) {
	fs := flag.NewFlagSet("cmdhist", flag.ExitOnError)
	shell := fs.String("shell", "", "bash|zsh|powershell (auto-detect if empty)")
	n := fs.Int("n", 30, "show last N commands")
	runIdx := fs.Int("run", 0, "index to re-run from shown list (1..N)")
	fs.Parse(args)

	h := collectShellHistory(*shell)
	if len(h) == 0 {
		fmt.Println("no history found")
		return
	}
	// show last n
	start := len(h) - *n
	if start < 0 {
		start = 0
	}
	sub := h[start:]
	for i := 0; i < len(sub); i++ {
		fmt.Printf("[%d] %s\n", i+1, sub[i])
	}
	if *runIdx > 0 {
		idx := *runIdx - 1
		if idx < 0 || idx >= len(sub) {
			fmt.Println("invalid run index")
			return
		}
		cmdStr := sub[idx]
		fmt.Printf("About to run: %s\nType YES to proceed: ", cmdStr)
		var resp string
		fmt.Scanln(&resp)
		if resp != "YES" {
			fmt.Println("aborted")
			return
		}
		// run via shell
		var sh, arg string
		if runtime.GOOS == "windows" {
			sh = "cmd"
			arg = "/C"
		} else {
			sh = "sh"
			arg = "-c"
		}
		c := exec.Command(sh, arg, cmdStr)
		c.Stdout = os.Stdout
		c.Stderr = os.Stderr
		c.Stdin = os.Stdin
		_ = c.Run()
	}
}

func collectShellHistory(shellFlag string) []string {
	home, _ := os.UserHomeDir()
	candidates := []string{}
	if shellFlag != "" {
		switch shellFlag {
		case "bash":
			candidates = append(candidates, filepath.Join(home, ".bash_history"))
		case "zsh":
			candidates = append(candidates, filepath.Join(home, ".zsh_history"))
		case "powershell":
			candidates = append(candidates, filepath.Join(home, "AppData", "Roaming", "Microsoft", "Windows", "PowerShell", "PSReadline", "ConsoleHost_history.txt"))
		}
	} else {
		// autodetect
		candidates = append(candidates, filepath.Join(home, ".bash_history"))
		candidates = append(candidates, filepath.Join(home, ".zsh_history"))
		candidates = append(candidates, filepath.Join(home, ".local", "share", "chezmoi", "history")) // just in case
		candidates = append(candidates, filepath.Join(home, "AppData", "Roaming", "Microsoft", "Windows", "PowerShell", "PSReadline", "ConsoleHost_history.txt"))
	}
	for _, c := range candidates {
		if _, err := os.Stat(c); err == nil {
			// read and return lines
			b, _ := ioutil.ReadFile(c)
			lines := []string{}
			sc := bufio.NewScanner(bytes.NewReader(b))
			for sc.Scan() {
				lines = append(lines, sc.Text())
			}
			// If zsh with timestamps, try strip : 160000:0;cmd
			for i, l := range lines {
				if strings.Contains(l, ";") && strings.HasPrefix(l, ": ") {
					parts := strings.SplitN(l, ";", 2)
					if len(parts) == 2 {
						lines[i] = parts[1]
					}
				}
			}
			return lines
		}
	}
	return nil
}

// -------------------- convert CSV <-> JSON <-> YAML <-> TOML --------------------

func convertCmd(args []string) {
	fs := flag.NewFlagSet("convert", flag.ExitOnError)
	sub := fs.String("sub", "", "subcommand: csv2json json2csv json2yaml yaml2json json2toml toml2json")
	in := fs.String("in", "", "input file path (default stdin)")
	out := fs.String("out", "", "output file path (default stdout)")
	fs.Parse(args)

	if *sub == "" {
		fmt.Println("usage: myutil convert -sub <sub> [-in file] [-out file]")
		return
	}
	var input []byte
	var err error
	if *in != "" {
		input, err = ioutil.ReadFile(*in)
		if err != nil {
			fmt.Printf("read error: %v\n", err)
			return
		}
	} else {
		input, _ = ioutil.ReadAll(os.Stdin)
	}

	var output []byte
	switch *sub {
	case "csv2json":
		output, err = csvToJSON(input)
	case "json2csv":
		output, err = jsonToCSV(input)
	case "json2yaml":
		var v interface{}
		if err = json.Unmarshal(input, &v); err == nil {
			output, err = yaml.Marshal(v)
		}
	case "yaml2json":
		var v interface{}
		if err = yaml.Unmarshal(input, &v); err == nil {
			output, err = json.MarshalIndent(v, "", "  ")
		}
	case "json2toml":
		var v interface{}
		if err = json.Unmarshal(input, &v); err == nil {
			output, err = toml.Marshal(v)
		}
	case "toml2json":
		var v interface{}
		if err = toml.Unmarshal(input, &v); err == nil {
			output, err = json.MarshalIndent(v, "", "  ")
		}
	default:
		fmt.Println("unknown sub")
		return
	}
	if err != nil {
		fmt.Printf("convert error: %v\n", err)
		return
	}
	if *out != "" {
		ioutil.WriteFile(*out, output, 0644)
	} else {
		fmt.Println(string(output))
	}
}

func csvToJSON(input []byte) ([]byte, error) {
	r := csv.NewReader(bytes.NewReader(input))
	rows, err := r.ReadAll()
	if err != nil {
		return nil, err
	}
	if len(rows) == 0 {
		return []byte("[]"), nil
	}
	headers := rows[0]
	arr := []map[string]string{}
	for _, row := range rows[1:] {
		m := map[string]string{}
		for i := 0; i < len(headers) && i < len(row); i++ {
			m[headers[i]] = row[i]
		}
		arr = append(arr, m)
	}
	return json.MarshalIndent(arr, "", "  ")
}

func jsonToCSV(input []byte) ([]byte, error) {
	var arr []map[string]interface{}
	if err := json.Unmarshal(input, &arr); err == nil {
		if len(arr) == 0 {
			return []byte(""), nil
		}
		// collect headers
		headerMap := map[string]struct{}{}
		for _, obj := range arr {
			for k := range obj {
				headerMap[k] = struct{}{}
			}
		}
		headers := []string{}
		for k := range headerMap {
			headers = append(headers, k)
		}
		sort.Strings(headers)
		b := &bytes.Buffer{}
		w := csv.NewWriter(b)
		_ = w.Write(headers)
		for _, obj := range arr {
			row := []string{}
			for _, h := range headers {
				if v, ok := obj[h]; ok {
					row = append(row, fmt.Sprint(v))
				} else {
					row = append(row, "")
				}
			}
			_ = w.Write(row)
		}
		w.Flush()
		return b.Bytes(), nil
	}
	// try object -> single-row csv
	var obj map[string]interface{}
	if err := json.Unmarshal(input, &obj); err == nil {
		headers := []string{}
		for k := range obj {
			headers = append(headers, k)
		}
		sort.Strings(headers)
		b := &bytes.Buffer{}
		w := csv.NewWriter(b)
		_ = w.Write(headers)
		row := []string{}
		for _, h := range headers {
			row = append(row, fmt.Sprint(obj[h]))
		}
		_ = w.Write(row)
		w.Flush()
		return b.Bytes(), nil
	}
	return nil, errors.New("invalid JSON input for csv conversion")
}

// -------------------- passgen + entropy tester --------------------

func passGenCmd(args []string) {
	fs := flag.NewFlagSet("passgen", flag.ExitOnError)
	length := fs.Int("len", 16, "password length")
	noSym := fs.Bool("no-symbols", false, "do not include symbols")
	fs.Parse(args)
	pass := generatePassword(*length, !*noSym)
	fmt.Println(pass)
	entropy := estimateEntropy(pass)
	fmt.Printf("estimated entropy: %.2f bits\n", entropy)
	// show rough crack time (very approximate)
	guessesPerSec := math.Pow10(6) // 1M guesses/s
	seconds := math.Pow(2, entropy) / guessesPerSec
	fmt.Printf("approx time @1M guesses/sec: %s\n", humanDuration(time.Duration(seconds)*time.Second))
}

func generatePassword(length int, useSymbols bool) string {
	lower := "abcdefghijklmnopqrstuvwxyz"
	upper := "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
	digits := "0123456789"
	symbols := "!@#$%^&*()-_=+[]{}<>?/~"

	pool := lower + upper + digits
	if useSymbols {
		pool += symbols
	}
	b := make([]byte, length)
	for i := range b {
		b[i] = pool[rand.Intn(len(pool))]
	}
	return string(b)
}

func estimateEntropy(s string) float64 {
	pool := 0
	if strings.IndexFunc(s, func(r rune) bool { return r >= 'a' && r <= 'z' }) >= 0 {
		pool += 26
	}
	if strings.IndexFunc(s, func(r rune) bool { return r >= 'A' && r <= 'Z' }) >= 0 {
		pool += 26
	}
	if strings.IndexFunc(s, func(r rune) bool { return r >= '0' && r <= '9' }) >= 0 {
		pool += 10
	}
	if strings.IndexFunc(s, func(r rune) bool { return strings.ContainsRune("!@#$%^&*()-_=+[]{}<>?/~", r) }) >= 0 {
		pool += 32
	}
	if pool == 0 {
		return 0
	}
	return float64(len(s)) * math.Log2(float64(pool))
}

func humanDuration(d time.Duration) string {
	if d < time.Second {
		return d.String()
	}
	secs := int64(d.Seconds())
	if secs < 60 {
		return fmt.Sprintf("%ds", secs)
	}
	mins := secs / 60
	if mins < 60 {
		return fmt.Sprintf("%dm%ds", mins, secs%60)
	}
	h := mins / 60
	return fmt.Sprintf("%dh%dm", h, mins%60)
}

// -------------------- password vault (encrypted) --------------------

func passVaultCmd(args []string) {
	fs := flag.NewFlagSet("passvault", flag.ExitOnError)
	sub := fs.String("sub", "", "create|add|get|list|delete")
	name := fs.String("name", "", "entry name")
	username := fs.String("user", "", "username")
	pass := fs.String("pass", "", "password (if empty will prompt/generate)")
	note := fs.String("note", "", "note")
	del := fs.Bool("yes", false, "confirm delete")
	fs.Parse(args)

	if *sub == "" {
		fmt.Println("usage: myutil passvault -sub <create|add|get|list|delete> [flags]")
		return
	}
	switch *sub {
	case "create":
		if _, err := os.Stat(appPath(vaultFileName)); err == nil {
			fmt.Println("Vault exists. use add/get/list/delete.")
			return
		}
		fmt.Println("Creating new vault.")
		master := promptPassword("Enter master password: ")
		confirm := promptPassword("Confirm master password: ")
		if master != confirm {
			fmt.Println("passwords do not match")
			return
		}
		v := Vault{Entries: []VaultEntry{}}
		if err := saveVault(v, master); err != nil {
			fmt.Printf("save error: %v\n", err)
		} else {
			fmt.Println("vault created.")
		}
	case "add":
		if *name == "" {
			fmt.Println("name required")
			return
		}
		var passwordVal string
		if *pass != "" {
			passwordVal = *pass
		} else {
			// ask: generate or prompt
			fmt.Print("Leave empty to generate, or type password: ")
			reader := bufio.NewReader(os.Stdin)
			line, _ := reader.ReadString('\n')
			line = strings.TrimSpace(line)
			if line == "" {
				passwordVal = generatePassword(20, true)
				fmt.Printf("generated: %s\n", passwordVal)
			} else {
				passwordVal = line
			}
		}
		master := promptPassword("Enter master password: ")
		v, err := loadVault(master)
		if err != nil {
			fmt.Printf("vault load error: %v\n", err)
			return
		}
		v.Entries = append(v.Entries, VaultEntry{
			Name:     *name,
			Username: *username,
			Password: passwordVal,
			Note:     *note,
		})
		if err := saveVault(v, master); err != nil {
			fmt.Printf("save error: %v\n", err)
		} else {
			fmt.Println("entry added.")
		}
	case "list":
		master := promptPassword("Enter master password: ")
		v, err := loadVault(master)
		if err != nil {
			fmt.Printf("vault load error: %v\n", err)
			return
		}
		for i, e := range v.Entries {
			fmt.Printf("[%d] %s  user=%s note=%s\n", i+1, e.Name, e.Username, previewLine(e.Note, 60))
		}
	case "get":
		if *name == "" {
			fmt.Println("name required")
			return
		}
		master := promptPassword("Enter master password: ")
		v, err := loadVault(master)
		if err != nil {
			fmt.Printf("vault load error: %v\n", err)
			return
		}
		for _, e := range v.Entries {
			if e.Name == *name {
				fmt.Printf("Name: %s\nUser: %s\nPassword: %s\nNote: %s\n", e.Name, e.Username, e.Password, e.Note)
				// also copy password to clipboard
				_ = clipboardCopy(e.Password)
				fmt.Println("(password copied to clipboard if supported)")
				return
			}
		}
		fmt.Println("entry not found")
	case "delete":
		if *name == "" {
			fmt.Println("name required")
			return
		}
		if !*del {
			fmt.Println("dangerous: confirm with -yes")
			return
		}
		master := promptPassword("Enter master password: ")
		v, err := loadVault(master)
		if err != nil {
			fmt.Printf("vault load error: %v\n", err)
			return
		}
		narr := []VaultEntry{}
		found := false
		for _, e := range v.Entries {
			if e.Name == *name {
				found = true
				continue
			}
			narr = append(narr, e)
		}
		if !found {
			fmt.Println("entry not found")
			return
		}
		v.Entries = narr
		if err := saveVault(v, master); err != nil {
			fmt.Printf("save error: %v\n", err)
		} else {
			fmt.Println("deleted")
		}
	default:
		fmt.Println("unknown sub")
	}
}

func promptPassword(prompt string) string {
	fmt.Print(prompt)
	// try to disable echo if possible
	if runtime.GOOS == "windows" {
		// fallback simple
		reader := bufio.NewReader(os.Stdin)
		s, _ := reader.ReadString('\n')
		return strings.TrimSpace(s)
	} else {
		// use stty to turn off echo
		fmt.Print(" ")
		cmd := exec.Command("sh", "-c", "stty -echo; read -r PASS; stty echo; echo $PASS")
		cmd.Stdin = os.Stdin
		out, err := cmd.Output()
		fmt.Println()
		if err == nil {
			return strings.TrimSpace(string(out))
		}
		// fallback
		reader := bufio.NewReader(os.Stdin)
		s, _ := reader.ReadString('\n')
		return strings.TrimSpace(s)
	}
}

func vaultKeyFromPassword(pass string, salt []byte) ([]byte, error) {
	return scrypt.Key([]byte(pass), salt, 1<<15, 8, 1, 32)
}

func saveVault(v Vault, master string) error {
	// marshal JSON
	b, err := json.Marshal(v)
	if err != nil {
		return err
	}
	// ensure salt exists
	saltPath := appPath(vaultSaltName)
	var salt []byte
	if _, err := os.Stat(saltPath); os.IsNotExist(err) {
		salt = make([]byte, 16)
		if _, err := rand.Read(salt); err != nil {
			return err
		}
		ioutil.WriteFile(saltPath, salt, 0600)
	} else {
		salt, _ = ioutil.ReadFile(saltPath)
	}
	key, err := vaultKeyFromPassword(master, salt)
	if err != nil {
		return err
	}
	// encrypt using AES-GCM
	block, err := aes.NewCipher(key)
	if err != nil {
		return err
	}
	aesg, err := cipher.NewGCM(block)
	if err != nil {
		return err
	}
	nonce := make([]byte, aesg.NonceSize())
	_, _ = rand.Read(nonce)
	ct := aesg.Seal(nil, nonce, b, nil)
	enc := append(nonce, ct...)
	// compute HMAC for basic integrity (using key)
	h := hmac.New(sha256.New, key)
	h.Write(enc)
	mac := h.Sum(nil)
	final := append(mac, enc...)
	return ioutil.WriteFile(appPath(vaultFileName), final, 0600)
}

func loadVault(master string) (Vault, error) {
	var v Vault
	final, err := ioutil.ReadFile(appPath(vaultFileName))
	if err != nil {
		return v, err
	}
	salt, err := ioutil.ReadFile(appPath(vaultSaltName))
	if err != nil {
		return v, err
	}
	key, err := vaultKeyFromPassword(master, salt)
	if err != nil {
		return v, err
	}
	if len(final) < sha256.Size {
		return v, errors.New("invalid vault")
	}
	mac := final[:sha256.Size]
	enc := final[sha256.Size:]
	h := hmac.New(sha256.New, key)
	h.Write(enc)
	if !hmac.Equal(mac, h.Sum(nil)) {
		return v, errors.New("invalid master password or corrupted vault")
	}
	// decrypt
	block, err := aes.NewCipher(key)
	if err != nil {
		return v, err
	}
	aesg, err := cipher.NewGCM(block)
	if err != nil {
		return v, err
	}
	if len(enc) < aesg.NonceSize() {
		return v, errors.New("invalid ciphertext")
	}
	nonce := enc[:aesg.NonceSize()]
	ct := enc[aesg.NonceSize():]
	plain, err := aesg.Open(nil, nonce, ct, nil)
	if err != nil {
		return v, err
	}
	if err := json.Unmarshal(plain, &v); err != nil {
		return v, err
	}
	return v, nil
}

// -------------------- gitignore generator --------------------

var gitignoreTemplates = map[string]string{
	"golang": `# Go
*.exe
*.dll
*.so
*.dylib
vendor/
bin/
*.test
*.out
`,
	"node": `# Node
node_modules/
dist/
.env
npm-debug.log
yarn-error.log
`,
	"python": `# Python
__pycache__/
*.py[cod]
*.egg-info/
dist/
build/
.env
`,
	"java": `# Java
*.class
*.jar
target/
`,
	"rust": `# Rust
/target
**/*.rs.bk
Cargo.lock
`,
	"unity": `# Unity
[Ll]ibrary/
[Tt]emp/
[Bb]uild/
[Bb]uilds/
`,
	"default": `# default .gitignore
.DS_Store
.idea/
.vscode/
*.log
`,
}

func gitignoreCmd(args []string) {
	fs := flag.NewFlagSet("gitignore", flag.ExitOnError)
	fs.Parse(args)
	if fs.NArg() < 1 {
		fmt.Println("usage: myutil gitignore <language>")
		return
	}
	lang := strings.ToLower(fs.Arg(0))
	if t, ok := gitignoreTemplates[lang]; ok {
		fmt.Print(t)
	} else {
		fmt.Print(gitignoreTemplates["default"])
	}
}
