#!/usr/bin/env python3

import re
import os
import sys

b_color_yellow = '\033[93m'
b_color_reset = '\033[0m'

curr_dir = os.path.dirname(os.path.realpath(__file__))
src_dir = f"{curr_dir}/../src"

nocheck_regex = re.compile("\\s*\\(\\*\\s*\\@nocheck\\s+(([a-z]|[A-Z]|[0-9])+)\\s*\\*\\)")

class Warning:
  line_no : int = 0
  type : str
  file : str = ""

  def __init__(self, line_no : int, type: str, file : str):
    self.file = file
    self.type = type
    self.line_no = line_no

  def _fmt_file(self) -> str:
    prefix, _, postfix = self.file.partition(".hooks/../") # strip going into the hooks directory
    return prefix + postfix

  def __str__(self) -> str:
    return f"{b_color_yellow}Warning: @nocheck {self.type} found: {b_color_reset}({self._fmt_file()}:{self.line_no})"
    pass

def validate_file(file) -> list[Warning]:
  warnings : list[Warning] = list()
  with open(file) as lines:
    for (line_no, line) in enumerate(lines, 1):
      match = re.match(nocheck_regex, line)
      if match:
        warnings.append(Warning(line_no, match.groups()[0], file))
  return warnings


all_warnings : list[Warning] = list()

args = sys.argv[1:]

print(f"Checking {args} for any files containing @nochecks ...")
for arg in args:
  all_warnings += validate_file(arg)


if not all_warnings:
  print("No warnings found")

num_violations = len(all_warnings)

for (n, violation) in enumerate(all_warnings, 1):
  print(f"({n}/{num_violations}) {violation}")
