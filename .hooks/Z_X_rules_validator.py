#!/usr/bin/env python3

import re
import os
import sys


MIN_PYTHON = (3, 10)
if sys.version_info < MIN_PYTHON:
  print(f"Your python version is {sys.version_info.major}.{sys.version_info.minor}. {MIN_PYTHON[0]}.{MIN_PYTHON[1]} is required")
  exit(3)


b_color_yellow = '\033[93m'
b_color_reset = '\033[0m'

curr_dir = os.path.dirname(os.path.realpath(__file__))

Z_rules_file_name = "ZRules.v"
X_rules_file_name = "XRules.v"
ZX_rules_file_name = "ZXRules.v"

print(f"Checking lemmas in {Z_rules_file_name}, {X_rules_file_name}, and {ZX_rules_file_name} for inconsistencies...")

Z_rules_file = f"{curr_dir}/../src/CoreRules/{Z_rules_file_name}"
X_rules_file = f"{curr_dir}/../src/CoreRules/{X_rules_file_name}"
ZX_rules_file = f"{curr_dir}/../src/CoreRules/{ZX_rules_file_name}"


duals : dict[str, str] = { 'X': 'Z','Z': 'X', 'X_Z': 'Z_X', 'Z_X' : 'X_Z' }

thm_token = "Theorem|Lemma|Fact|Remark|Corollary|Proposition|Property"
exists_thm_regex = re.compile(f".*({thm_token})\\s*(([a-z]|[A-Z]|_)([a-z]|[A-Z]|_|-|\\d)+)")

ignore_regex = re.compile("\\s*\\(\\*\\s*\\@nocheck\\s+Z\\_X\\s*\\*\\)")

def is_ignore(line : str) -> bool:
  return re.match(ignore_regex, line)
  
def get_theorem(line : str) -> str:
  match = re.match(exists_thm_regex, line)
  if not match:
    return ""
  return  match.groups()[1]  

def check_qualification(thms : set[str], quals : list[str]) -> list[str]:
  violations = list()
  for thm in thms:
    qual_found = False
    for qual in quals:
      if f"{qual}_" in thm:
        qual_found = True
        break
    if not qual_found:
      violations.append(thm)
  return violations

def check_all_in_other(thms : set[str], other : set[str], qual : str) -> list[str]:
  violations = list()
  for thm in thms:
    if thm.replace(qual + "_", duals[qual] + "_") not in other:
      violations.append(thm)
  return violations

def check_Z_X_has_duals(thms : set[str]) -> list[str]:
  violations = list()
  violations += check_all_in_other(thms, thms, 'Z_X')
  violations += check_all_in_other(thms, thms, 'X_Z')
  restr_thms = set(filter(lambda thm : 'Z_X' not in thm and 'X_Z' not in thm, thms))
  violations += check_all_in_other(restr_thms, restr_thms, 'Z')
  violations += check_all_in_other(restr_thms, restr_thms, 'X')
  return violations

def read_thms(file_str) -> set[str]:
  thms = set()
  with open(file_str) as rules:
    skip_next = False
    for line in rules:
      if is_ignore(line):
        skip_next = True
        continue
      thm = get_theorem(line)
      if skip_next:
        skip_next = False
        continue
      if thm != "":
        thms.add(thm)
  return thms

Z_rules_thms : set[str] = read_thms(Z_rules_file)
X_rules_thms : set[str] = read_thms(X_rules_file)
ZX_rules_thms : set[str] = read_thms(ZX_rules_file)

Z_qual_violation = check_qualification(Z_rules_thms, ['Z'])
X_qual_violation = check_qualification(X_rules_thms, ['X'])
Z_total_violation = check_all_in_other(Z_rules_thms, X_rules_thms, 'Z')
X_total_violation = check_all_in_other(X_rules_thms, Z_rules_thms, 'X')
ZX_qual_violations = check_qualification(ZX_rules_thms, duals.keys())
ZX_duals_violations = check_Z_X_has_duals(ZX_rules_thms)

print(b_color_yellow, end='')
for violation in Z_qual_violation:
  print(f'The lemma "{violation}" in {Z_rules_file_name} violates the rule that each lemma in this file must be described as a Z lemma (i.e., contain "Z_") - suggestion: Rename to Z_{violation}')

for violation in X_qual_violation:
  print(f'The lemma "{violation}" in {X_rules_file_name} violates the rule that each lemma in this file must be described as an X lemma (i.e., contain "X_") - suggestion: Rename to X_{violation}')

for violation in Z_total_violation:
  if violation not in Z_qual_violation: # Can't find anything if lemma is incorrectly named
    print(f'The lemma "{violation}" violates the rule that each lemma in {Z_rules_file_name} must also be in {X_rules_file_name} under the same name up to the change of Z_ to X_')

for violation in X_total_violation:
  if violation not in X_qual_violation: # Can't find anything if lemma is incorrectly named
    print(f'The lemma "{violation}" violates the rule that each lemma in {X_rules_file_name} must also be in {Z_rules_file_name} under the same name up to the change of X_ to Z_')

for violation in ZX_qual_violations:
  print(f'The lemma "{violation}" in {ZX_rules_file_name} violates the rule that each lemma in this file must be described as an Z, X, Z_X or X_Z lemma - suggestion: Rename to [Z, X, Z_X or X_Z]_{violation}')

for violation in ZX_duals_violations:
  if violation not in ZX_qual_violations:
    print(f'The lemma "{violation}" violates the rule that each lemma in {ZX_rules_file_name} must also have its colorswapped version')
print(b_color_reset, end='')

all_violations = [Z_qual_violation, X_qual_violation, Z_total_violation, X_total_violation, ZX_qual_violations, ZX_duals_violations]
if not any(all_violations):
  print("No violations found...")
  exit(0)

print("Done...")
exit(1)

