#ifndef DEKO_IOCTL_H
#define DEKO_IOCTL_H

#include <linux/ioctl.h>
#include <linux/types.h>

#define DEKO_IOC_MAGIC 0xDD

struct deko_domain_binding {
  __u64 mnt_ns_id;
  __u32 domain_id;
  __u32 flags;
};

struct deko_domain_lookup {
  __u64 mnt_ns_id;
  __u32 domain_id;
  __u32 found;
};

#define DEKO_IOC_BIND_DOMAIN                                                   \
  _IOW(DEKO_IOC_MAGIC, 0x01, struct deko_domain_binding)
#define DEKO_IOC_LOOKUP_DOMAIN                                                 \
  _IOWR(DEKO_IOC_MAGIC, 0x02, struct deko_domain_lookup)
#define DEKO_IOC_UNBIND_DOMAIN                                                 \
  _IOW(DEKO_IOC_MAGIC, 0x03, struct deko_domain_binding)

#endif /* DEKO_IOCTL_H */
