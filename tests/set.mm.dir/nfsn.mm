include "csn.mm"
include "cpr.mm"
include "dfsn2.mm"
include "nfpr.mm"
include "nfcxfr.mm"

theorem nfsn
  let vx: setvar x
  let cA: class A
  assume nfsn.1: |- F/_ x A


  assert |- F/_ x { A }

  proof
    vx
    cA
    csn
    cA
    cA
    cpr
    cA
    dfsn2
    vx
    cA
    cA
    nfsn.1
    nfsn.1
    nfpr
    nfcxfr
end
