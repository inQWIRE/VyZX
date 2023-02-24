#!/usr/bin/env python3

import re
import os

curr_dir = os.path.dirname(os.path.realpath(__file__))

Z_rules_file_name = "ZRules.v"
X_rules_file_name = "XRules.v"

print(f"Checking lemmas in {Z_rules_file_name} and {X_rules_file_name} for inconsistencies...")

Z_rules_file = f"{curr_dir}/../src/CoreRules/{Z_rules_file_name}"
X_rules_file = f"{curr_dir}/../src/CoreRules/{X_rules_file_name}"

Z_rules_thms : set[str] = set()
X_rules_thms : set[str] = set()

def get_theorem(line : str) -> str:
  thm_token = "Theorem|Lemma|Fact|Remark|Corollary|Proposition|Property"
  exists_thm_regex = f".*({thm_token})\\s*(([a-z]|[A-Z]|_)([a-z]|[A-Z]|_|-|\\d)+)"
  match = re.match(exists_thm_regex, line)
  if not match:
    return ""
  return  match.groups()[1]  

with open(Z_rules_file) as Z_rules:
  for line in Z_rules:
    thm = get_theorem(line)
    if thm != "":
      Z_rules_thms.add(thm)

with open(X_rules_file) as X_rules:
  for line in X_rules:
    thm = get_theorem(line)
    if thm != "":
      X_rules_thms.add(thm)

def check_qualification(thms : set[str], qual : str) -> list:
  violations = list()
  for thm in thms:
    if f"{qual}_" not in thm:
      violations.append(thm)
  return violations

def check_all_in_other(thms : set[str], other : set[str], qual : str, other_qual : str) -> list:
  violations = list()
  for thm in thms:
    if thm.replace(qual, other_qual) not in other:
      violations.append(thm)
  return violations

Z_qual_violation = check_qualification(Z_rules_thms, 'Z')
X_qual_violation = check_qualification(X_rules_thms, 'X')
Z_total_violation = check_all_in_other(Z_rules_thms, X_rules_thms, 'Z_', 'X_')
X_total_violation = check_all_in_other(X_rules_thms, Z_rules_thms, 'X_', 'Z_')

if Z_qual_violation:
  for violaton in Z_qual_violation:
    print(f'The lemma "{violaton}" in {Z_rules_file_name} violates the rule that each lemma in this file must be described as a Z lemma (i.e., contain "Z_")')

if X_qual_violation:
  for violaton in X_qual_violation:
    print(f'The lemma "{violaton}" in {X_rules_file_name} violates the rule that each lemma in this file must be described as an X lemma (i.e., contain "X_")')

if Z_total_violation:
  for violaton in Z_total_violation:
    if violaton not in Z_qual_violation: # Can't find anything if lemma is incorrectly named
      print(f'The lemma "{violaton}" violates the rule that each lemma in {Z_rules_file_name} must also be in {X_rules_file_name} under the same name up to the change of Z_ to X_')

if X_total_violation:
  for violaton in X_total_violation:
    if violaton not in X_qual_violation: # Can't find anything if lemma is incorrectly named
      print(f'The lemma "{violaton}" violates the rule that each lemma in {X_rules_file_name} must also be in {Z_rules_file_name} under the same name up to the change of X_ to Z_')

if not (Z_qual_violation or X_qual_violation or Z_total_violation or X_total_violation):
  print("No violations found...")
  exit(0)

print("Done...")
exit(1)

