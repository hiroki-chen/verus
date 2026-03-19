# Copyright 2026 Hiroki Chen and the Deko Authors
#
# This file includes all the metadata for authoring policies in Deko which targets flexible
# Information Flow Control (IFC) policies. The metadata is a helper to define sensitivity
# labels, tags, and other attributes that can be used in the policies.

package deko.ifc.metadata

labels := {"top_secret": 3, "secret": 2, "internal": 1, "public": 0}

# Restricted resources.
resources := {
    "foo": {"label": "secret", "type": "file" },
}

entities := {
}

source_syscalls := [
    "read", "recv", "recvfrom", "recvmsg",
    "connect", "accept", "accept4",
]

sink_syscalls := [
    "write", "send", "sendto", "sendmsg",
]
