#include <cactus_rt/rt.h>
#include <spdlog/spdlog.h>
#include <unistd.h>

class MyThread : public cactus_rt::CyclicThread<cactus_rt::schedulers::Fifo> {
  int n_ = 0;

 public:
  MyThread(std::vector<size_t> cpu_affinity)
      : cactus_rt::CyclicThread<cactus_rt::schedulers::Fifo>("MyThread", 1'000'000, /* Period */
                                                             cactus_rt::schedulers::Fifo::Config{80 /* Priority */},
                                                             cpu_affinity) {}

  int Result() const {
    return n_;
  }

 protected:
  bool Loop(int64_t /*now*/) noexcept final {
    {
      TRACE_EVENT(cactus_rt::kTracingCategoryRealTime, "MyThread::Region1");
      n_ += NumFactors(30000);
    }

    {
      TRACE_EVENT(cactus_rt::kTracingCategoryRealTime, "MyThread::Region2");
      n_ += NumFactors(150000);
    }

    {
      TRACE_EVENT(cactus_rt::kTracingCategoryRealTime, "MyThread::Region3");
      n_ += NumFactors(90000);
    }

    return false;
  }

 private:
  int NumFactors(int n) {
    int c = 0;
    for (int i = 1; i < n; i++) {
      if (n % i == 0) {
        c++;
      }
    }

    return c;
  }
};

class RTApp : public cactus_rt::App {
  MyThread thread_;

 public:
  RTApp(std::vector<size_t> cpu_affinity) : thread_(cpu_affinity) {
    RegisterThread(thread_);
  }

  int Result() const {
    return thread_.Result();
  }
};

int main() {
  spdlog::set_level(spdlog::level::debug);

  RTApp app(std::vector<size_t>{2});

  constexpr unsigned int time = 5;
  SPDLOG_INFO("Testing latency for {}s", time);
  app.Start();
  sleep(time);
  app.RequestStop();
  app.Join();
  SPDLOG_INFO("result: {}", app.Result());
  return 0;
}
