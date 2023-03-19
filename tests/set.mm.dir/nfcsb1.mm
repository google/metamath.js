include "csb.mm"
include "wnfc.mm"
include "wtru.mm"
include "a1i.mm"
include "nfcsb1d.mm"
include "trud.mm"

theorem nfcsb1
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume nfcsb1.1: |- F/_ x A


  assert |- F/_ x [_ A / x ]_ B

  proof
    vx
    vx
    cA
    cB
    csb
    wnfc
    wtru
    vx
    cA
    cB
    vx
    cA
    wnfc
    wtru
    nfcsb1.1
    a1i
    nfcsb1d
    trud
end
