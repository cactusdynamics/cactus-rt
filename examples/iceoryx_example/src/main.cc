#include "app.h"
#include "publisher.h"
#include "subscriber.h"

int main() {
  // App must be created first, as the iceoryx runtime is defined there first.
  App                         app;
  std::unique_ptr<Subscriber> sub{std::make_unique<Subscriber>()};
  std::unique_ptr<Publisher>  pub{std::make_unique<Publisher>()};

  app.RegisterThread(std::move(sub));
  app.RegisterThread(std::move(pub));

  app.Start();
  app.Join();
  return 0;
}
