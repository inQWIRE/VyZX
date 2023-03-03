#!/usr/bin/env python3

import re
import os

b_color_yellow = '\033[93m'
b_color_reset = '\033[0m'

curr_dir = os.path.dirname(os.path.realpath(__file__))
src_dir = f"{curr_dir}/../src"

search_commands = "Search|Locate|About|Check|SearchPattern|SearchRewrite|Print"
search_regex = re.compile(f"\\s*({search_commands}).*")
ignore_regex = re.compile("\\s*\\(\\*\\s*\\@nocheck\\s+Search\\s*\\*\\)")

class Violation:
  line_no : int = 0
  line : str = ""
  file : str = ""
  keyword : str = ""

  def __init__(self, line_no : int, line : str, file : str, keyword : str):
    self.line = line
    self.file = file
    self.line_no = line_no
    self.keyword = keyword

  def _fmt_file(self) -> str:
    prefix, _, postfix = self.file.partition(".hooks/../") # strip going into the hooks directory
    return prefix + postfix

  def __str__(self) -> str:
    return f"{b_color_yellow}Violation found: \"{self.keyword}\" command should not be committed. {b_color_reset}({self._fmt_file()}:{self.line_no} - {self.line})"
    pass

def validate_file(file) -> list[Violation]:
  violations : list[Violation] = list()
  with open(file) as lines:
    skip_next = False
    for (line_no, line) in enumerate(lines, 1):
      if re.match(ignore_regex, line):
        skip_next = True
        continue
      match = re.match(search_regex, line)
      if match:
        if skip_next:
          skip_next = False
          continue
        violations.append(Violation(line_no, line.strip(), file, match.groups()[0]))
  return violations


print("Checking src/ directory for any files containing search or print statements...")
all_violations : list[Violation] = list()

for dir, _, files in os.walk(src_dir):
    for file in files:
      if not file.endswith(".v"): # Make sure we only look at Coq files
        continue
      all_violations += validate_file(f"{dir}/{file}")


if not all_violations:
  print("No violations found")
  exit(0)

num_violations = len(all_violations)

for (n, violation) in enumerate(all_violations, 1):
  print(f"({n}/{num_violations}) {violation}")

exit(1)