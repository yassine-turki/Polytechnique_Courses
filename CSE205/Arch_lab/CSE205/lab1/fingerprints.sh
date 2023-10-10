#!/bin/sh

#Name: Yassine Turki
#Userid: yassine.turki

# Sort the list of hostnames
sortedhosts=$(for host in "$@"; do
echo "$host"
done | sort)

# Table
printf '%s\t| %s\n' "Hostname" "Fingerprint" | expand -t 30
echo "------------------------------|---------------------------------------------------"

for host in $sortedhosts; do
  # Get the key for current host
  out=$(ssh-keyscan -t ecdsa "$host" 2>/dev/null)
  # Check if out is not empty
  if [ -n "$out" ]; then
    fingerprint=$(echo "$out" | ssh-keygen -l -f -)
    regex=($fingerprint)
    SHA256=${regex[1]}
    printf '%s\t| %s\n' "$host" "$SHA256" | expand -t 30
  else
    #Print ERROR
   printf '%s\t| %s\n' "$host" "ERROR" | expand -t 30
  fi
done

