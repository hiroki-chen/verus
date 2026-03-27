#include <linux/fs.h>
#include <linux/hashtable.h>
#include <linux/init.h>
#include <linux/kernel.h>
#include <linux/miscdevice.h>
#include <linux/module.h>
#include <linux/mutex.h>
#include <linux/slab.h>
#include <linux/uaccess.h>

#include "deko_ioctl.h"

#define DEKO_DOMAIN_BITS 8

struct deko_binding_entry {
  u64 mnt_ns_id;
  u32 domain_id;
  struct hlist_node node;
};

static DEFINE_HASHTABLE(deko_domain_table, DEKO_DOMAIN_BITS);
static DEFINE_MUTEX(deko_domain_lock);

static struct deko_binding_entry *deko_find_binding_locked(u64 mnt_ns_id) {
  struct deko_binding_entry *entry;

  hash_for_each_possible(deko_domain_table, entry, node, mnt_ns_id) {
    if (entry->mnt_ns_id == mnt_ns_id)
      return entry;
  }

  return NULL;
}

static long deko_bind_domain(const struct deko_domain_binding *binding) {
  struct deko_binding_entry *entry;

  if (binding->mnt_ns_id == 0 || binding->domain_id == 0)
    return -EINVAL;

  mutex_lock(&deko_domain_lock);

  entry = deko_find_binding_locked(binding->mnt_ns_id);
  if (entry) {
    if (entry->domain_id == binding->domain_id) {
      mutex_unlock(&deko_domain_lock);
      return 0;
    }

    mutex_unlock(&deko_domain_lock);
    return -EEXIST;
  }

  entry = kzalloc(sizeof(*entry), GFP_KERNEL);
  if (!entry) {
    mutex_unlock(&deko_domain_lock);
    return -ENOMEM;
  }

  entry->mnt_ns_id = binding->mnt_ns_id;
  entry->domain_id = binding->domain_id;
  hash_add(deko_domain_table, &entry->node, entry->mnt_ns_id);

  mutex_unlock(&deko_domain_lock);

  pr_info("deko: bind mnt_ns_id=%llu domain_id=%u\n", binding->mnt_ns_id,
          binding->domain_id);
  return 0;
}

static long deko_lookup_domain(struct deko_domain_lookup *lookup) {
  struct deko_binding_entry *entry;

  if (lookup->mnt_ns_id == 0)
    return -EINVAL;

  lookup->domain_id = 0;
  lookup->found = 0;

  mutex_lock(&deko_domain_lock);

  entry = deko_find_binding_locked(lookup->mnt_ns_id);
  if (entry) {
    lookup->domain_id = entry->domain_id;
    lookup->found = 1;
  }

  mutex_unlock(&deko_domain_lock);
  return 0;
}

static long deko_unbind_domain(const struct deko_domain_binding *binding) {
  struct deko_binding_entry *entry;

  if (binding->mnt_ns_id == 0)
    return -EINVAL;

  mutex_lock(&deko_domain_lock);

  entry = deko_find_binding_locked(binding->mnt_ns_id);
  if (!entry) {
    mutex_unlock(&deko_domain_lock);
    return -ENOENT;
  }

  if (binding->domain_id != 0 && entry->domain_id != binding->domain_id) {
    mutex_unlock(&deko_domain_lock);
    return -EEXIST;
  }

  hash_del(&entry->node);
  mutex_unlock(&deko_domain_lock);

  pr_info("deko: unbind mnt_ns_id=%llu domain_id=%u\n", entry->mnt_ns_id,
          entry->domain_id);
  kfree(entry);
  return 0;
}

static long deko_unlocked_ioctl(struct file *file, unsigned int cmd,
                                unsigned long arg) {
  switch (cmd) {
  case DEKO_IOC_BIND_DOMAIN: {
    struct deko_domain_binding binding;

    if (copy_from_user(&binding, (void __user *)arg, sizeof(binding)))
      return -EFAULT;

    return deko_bind_domain(&binding);
  }
  case DEKO_IOC_LOOKUP_DOMAIN: {
    struct deko_domain_lookup lookup;
    long ret;

    if (copy_from_user(&lookup, (void __user *)arg, sizeof(lookup)))
      return -EFAULT;

    ret = deko_lookup_domain(&lookup);
    if (ret)
      return ret;

    if (copy_to_user((void __user *)arg, &lookup, sizeof(lookup)))
      return -EFAULT;

    return 0;
  }
  case DEKO_IOC_UNBIND_DOMAIN: {
    struct deko_domain_binding binding;

    if (copy_from_user(&binding, (void __user *)arg, sizeof(binding)))
      return -EFAULT;

    return deko_unbind_domain(&binding);
  }
  default:
    return -ENOTTY;
  }
}

static const struct file_operations deko_fops = {
    .owner = THIS_MODULE,
    .unlocked_ioctl = deko_unlocked_ioctl,
#ifdef CONFIG_COMPAT
    .compat_ioctl = deko_unlocked_ioctl,
#endif
};

static struct miscdevice deko_miscdev = {
    .minor = MISC_DYNAMIC_MINOR,
    .name = "deko",
    .fops = &deko_fops,
    .mode = 0600,
};

static int __init deko_init(void) {
  hash_init(deko_domain_table);
  pr_info("deko: registering /dev/deko\n");
  return misc_register(&deko_miscdev);
}

static void __exit deko_exit(void) {
  struct deko_binding_entry *entry;
  struct hlist_node *tmp;
  int bucket;

  mutex_lock(&deko_domain_lock);
  hash_for_each_safe(deko_domain_table, bucket, tmp, entry, node) {
    hash_del(&entry->node);
    kfree(entry);
  }
  mutex_unlock(&deko_domain_lock);

  misc_deregister(&deko_miscdev);
  pr_info("deko: unregistered /dev/deko\n");
}

module_init(deko_init);
module_exit(deko_exit);

MODULE_LICENSE("GPL");
MODULE_AUTHOR("Hiroki Chen <haobchen@iu.edu>");
MODULE_DESCRIPTION(
    "Prototype /dev/deko device for mnt_ns_id to domain_id bindings");
