provider rt_demo {
  probe thread_start(int scheduler_policy, int soft_page_fault_count, int hard_page_fault_count);
  probe thread_done(int scheduler_policy, int soft_page_fault_count, int hard_page_fault_count);

  probe rt_iteration_start(long start_latency);
  probe rt_iteration_done(long iteration_latency);
};
