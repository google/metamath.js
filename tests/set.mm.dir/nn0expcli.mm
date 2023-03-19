include "cn0.mm"
include "wcel.mm"
include "cexp.mm"
include "co.mm"
include "nn0expcl.mm"
include "mp2an.mm"

theorem nn0expcli
  let cA: class A
  let cN: class N
  assume nn0expcli.1: |- A e. NN0
  assume nn0expcli.2: |- N e. NN0


  assert |- ( A ^ N ) e. NN0

  proof
    cA
    cn0
    wcel
    cN
    cn0
    wcel
    cA
    cN
    cexp
    co
    cn0
    wcel
    nn0expcli.1
    nn0expcli.2
    cA
    cN
    nn0expcl
    mp2an
end
