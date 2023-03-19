include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "negcl.mm"
include "ax-mp.mm"

theorem negcli
  let cA: class A
  assume negidi.1: |- A e. CC


  assert |- -u A e. CC

  proof
    cA
    cc
    wcel
    cA
    cneg
    cc
    wcel
    negidi.1
    cA
    negcl
    ax-mp
end
