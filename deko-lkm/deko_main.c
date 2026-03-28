#include <linux/fs.h>
#include <linux/init.h>
#include <linux/kernel.h>
#include <linux/miscdevice.h>
#include <linux/module.h>
#include <linux/slab.h>
#include <linux/uaccess.h>
#include <asm/sev.h>

#include "deko_ioctl.h"

extern int deko_domain_bind(u64 mnt_ns_id, u32 domain_id);
extern int deko_domain_lookup(u64 mnt_ns_id, u32 *domain_id);
extern int deko_domain_unbind(u64 mnt_ns_id, u32 domain_id);
extern int svsm_deko_load_policy(u32 domain_id, const void *buf, u64 len);

static long deko_bind_domain(const struct deko_domain_binding *binding) {
  if (binding->mnt_ns_id == 0 || binding->domain_id == 0)
    return -EINVAL;

  return deko_domain_bind(binding->mnt_ns_id, binding->domain_id);
}

static long deko_lookup_domain(struct deko_domain_lookup *lookup) {
  u32 domain_id = 0;
  int ret;

  if (lookup->mnt_ns_id == 0)
    return -EINVAL;

  lookup->domain_id = 0;
  lookup->found = 0;

  ret = deko_domain_lookup(lookup->mnt_ns_id, &domain_id);
  if (!ret) {
    lookup->domain_id = domain_id;
    lookup->found = 1;
    return 0;
  }
  if (ret == -ENOENT)
    return 0;
  return ret;
}

static long deko_unbind_domain(const struct deko_domain_binding *binding) {
  if (binding->mnt_ns_id == 0)
    return -EINVAL;
  return deko_domain_unbind(binding->mnt_ns_id, binding->domain_id);
}

static long deko_load_policy(const struct deko_load_policy *req) {
  void *policy_buf;
  int ret;

  if (req->domain_id == 0 || req->policy_ptr == 0 || req->policy_len == 0)
    return -EINVAL;

  policy_buf = memdup_user(u64_to_user_ptr(req->policy_ptr), req->policy_len);
  if (IS_ERR(policy_buf))
    return PTR_ERR(policy_buf);

  ret = svsm_deko_load_policy(req->domain_id, policy_buf, req->policy_len);
  kfree(policy_buf);
  return ret;
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
  case DEKO_IOC_LOAD_POLICY: {
    struct deko_load_policy req;

    if (copy_from_user(&req, (void __user *)arg, sizeof(req)))
      return -EFAULT;

    return deko_load_policy(&req);
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
  pr_info("deko: registering /dev/deko\n");
  return misc_register(&deko_miscdev);
}

static void __exit deko_exit(void) {
  misc_deregister(&deko_miscdev);
  pr_info("deko: unregistered /dev/deko\n");
}

module_init(deko_init);
module_exit(deko_exit);

MODULE_LICENSE("GPL");
MODULE_AUTHOR("Hiroki Chen <haobchen@iu.edu>");
MODULE_DESCRIPTION(
    "Prototype /dev/deko device for mnt_ns_id to domain_id bindings");
