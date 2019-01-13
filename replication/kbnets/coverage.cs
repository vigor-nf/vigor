// C# script to replicate coverage info from Table one, based on a 'run.istats' file of the KLEE output.

﻿using System;
using System.Collections.Generic;
using System.IO;

namespace InstrCounter
{
	class Program
	{
		public static readonly string[] libc_fns = {
		    "asctime", "asctime_r", "atoi", "closedir", "ctime", "dirfd", "__drand48_iterate", "fclose",
		    "__fgetc_unlocked", "fgets_unlocked", "_stdio_fopen", "fopen", "fprintf", "fscanf", "fwrite_unlocked",
		    "getenv", "_getopt_internal", "getopt_long", "_getopt_internal_r", "exchange", "_getopt_initialize", "isascii",
		    "localtime", "localtime_r", "lrand48", "memcmp", "memcpy", "memmove", "memset", "nrand48_r", "opendir", "__psfs_do_numeric",
		    "__psfs_parse_spec", "qsort", "readdir", "__stdio_READ", "__init_scan_cookie", "__scan_getc", "__scan_ungetc", "sigaddset",
		    "sigemptyset", "__sigaddset", "srand48", "srand48_r", "_stdlib_strto_l", "_store_inttype", "strcat", "strchr", "strcmp",
		    "strcpy", "strcspn", "strdup", "strerror", "strlen", "strncasecmp", "strncat", "strncmp", "strncpy", "strndup", "strnlen",
		    "strpbrk", "strrchr", "strsep", "strstr", "__strtofpmax", "strtol", "strtoul", "sysconf", "openlog", "vsyslog", "syslog",
		    "sigpipe_handler", "closelog_intern", "__time_localtime_tzi", "tm_isdst", "_time_t2tm", "__stdio_trans2r", "__stdio_trans2w",
		    "_time_tzset", "getoffset", "getnumber", "_uintmaxtostr", "ungetc", "vfscanf", "kill_scan_cookie", "__stdio_WRITE", "__xpg_strerror_r"
		};

		public static readonly string[] dsos_fns = {
		    "start_time", "clock_gettime", "restart_time", "current_time", "time", "sprintf", "snprintf", "vsnprintf", "printf", "vprintf",
		    "_vsnprintf", "_strlen", "_ftoa", "_ntoa_long", "_ntoa_format", "_ntoa_long_long", "_atoi", "_is_digit", "_out_null", "__sigsetjmp",
		    "timerfd_settime", "getpid", "numa_available", "numa_allocate_nodemask", "numa_bitmask_free", "get_mempolicy", "connect", "timerfd_create",
		    "eventfd", "epoll_create", "exit", "numa_set_preferred", "fnmatch", "set_mempolicy", "__libc_fcntl", "unlink", "fflush", "vfprintf",
		    "fopencookie", "write", "siglongjmp", "pwrite", "pipe", "stub_pipe_write", "unlinkat", "regcomp", "epoll_wait", "sleep", "getuid",
		    "syscall", "getpagesize", "sigaction", "epoll_ctl", "nanosleep", "access", "stat", "open", "fcntl", "flock", "fstat", "ftruncate", "lseek",
		    "read", "pread", "close", "readlink", "__getdents", "mmap", "munmap", "__libc_open", "stub_stdio_files_init", "stub_pci_name", "stub_add_file",
		    "stub_pci_file", "stub_add_link", "stub_add_folder", "stub_pci_addr", "stub_add_folder_array", "stub_pci_folder", "numa_set_localalloc",
		    "openat", "regexec", "mknod", "getdtablesize", "dlerror", "__ctype_b_loc", "pthread_self", "pthread_getaffinity_np", "pthread_setaffinity_np",
		    "pthread_create", "pthread_setname_np", "gnu_dev_makedev", "dlopen"
		};

		static void Main(string[] args)
		{
			string currentFunctionName = null;
			var counts = new Dictionary<string, (int, int)>();
			var lines = new HashSet<int>();
			var covered = 0;
			var uncovered = 0;
			var ignoreNext = false;
			foreach (var line in File.ReadLines("run.istats"))
			{
				if (ignoreNext)
				{
					ignoreNext = false;
					continue;
				}

				var parts = line.Split(" ");

				if (line.StartsWith("fn="))
				{
					if (currentFunctionName != null)
					{
						counts.Add(currentFunctionName, (covered, uncovered));
						covered = 0;
						uncovered = 0;
						lines = new HashSet<int>(); currentFunctionName = null;
					}

					currentFunctionName = line.Substring(3);

					continue;
				}
				else if (line.StartsWith("calls="))
				{
					// next is inclusive cost
					ignoreNext = true;
					continue;
				}
				else if (line.StartsWith("cfn=") || line.StartsWith("cfl=") || line.StartsWith("fl="))
				{
					continue; // Ignore, in the middle of a fn=
				}
				else if (!int.TryParse(parts[0], out int ignored))
				{
					// OK...
					Console.WriteLine("SKIP: " + line);
					continue;
				}

				var lineNumber = int.Parse(parts[0]);
				var lineCovered = int.Parse(parts[2]);
				var lineUncovered = int.Parse(parts[10]);

				if (lines.Add(lineNumber)) // only count a single instr per line
				{
					covered += lineCovered;
					uncovered += lineUncovered;
				}
			}

			var vignat = (0, 0);
			var dpdk = (0, 0);
			var ixgbe = (0, 0);
			var libc = (0, 0);
			var dsos = (0, 0);

			foreach (var (name, (cov, uncov)) in counts)
			{
				if (name.StartsWith("ixgbe_") || name.StartsWith("ixgbevf_"))
				{
					ixgbe = (ixgbe.Item1 + cov, ixgbe.Item2 + uncov);
				}
				else if (name.StartsWith("rte_") || name.StartsWith("vdev_") || name.StartsWith("pci_") || name.StartsWith("eal_")
						|| name.StartsWith("memzone_") || name.StartsWith("_rte") || name.StartsWith("__rte"))
				{
					dpdk = (dpdk.Item1 + cov, dpdk.Item2 + uncov);
				}
				else if (name.StartsWith("nf_") || name.StartsWith("nat_")
						|| name == "lcore_main" || name == "main"
						|| name == "allocate_flowmanager" || name == "allocate_flow" || name == "get_and_rejuvenate" || name == "get_flow_by_int_key"
						|| name == "get_flow_by_ext_key" || name == "expire_flows" || name == "get_flow" || name == "get_flow_int" || name == "get_flow_ext"
						|| name == "fill_int_key" || name == "fill_ext_key" || name == "add_flow" || name == "allocate_flowtables")
				{
					vignat = (vignat.Item1 + cov, vignat.Item2 + uncov);
				}
				else if (Array.IndexOf(libc_fns, name) > -1)
				{
					libc = (libc.Item1 + cov, libc.Item2 + uncov);
				}
				else if (name.StartsWith("dsos_") || Array.IndexOf(dsos_fns, name) > -1)
				{
					dsos = (dsos.Item1 + cov, dsos.Item2 + uncov);
				}
				else
				{
					Console.WriteLine("IGNORE: " + name);
				}
			}

			Console.WriteLine($"VigNAT: {vignat.Item1} covered, {vignat.Item2} uncovered, {vignat.Item1 + vignat.Item2} total");
			Console.WriteLine($"DPDK: {dpdk.Item1} covered, {dpdk.Item2} uncovered, {dpdk.Item1 + dpdk.Item2} total");
			Console.WriteLine($"ixgbe: {ixgbe.Item1} covered, {ixgbe.Item2} uncovered, {ixgbe.Item1 + ixgbe.Item2} total");
			Console.WriteLine($"libc: {libc.Item1} covered, {libc.Item2} uncovered, {libc.Item1 + libc.Item2} total");
			Console.WriteLine($"DSOS: {dsos.Item1} covered, {dsos.Item2} uncovered, {dsos.Item1 + dsos.Item2} total");
			Console.Read();
		}
	}
}
