include "csb.mm"
include "wnfc.mm"
include "wtru.mm"
include "nftru.mm"
include "a1i.mm"
include "nfcsbd.mm"
include "trud.mm"

theorem nfcsb
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume nfcsb.1: |- F/_ x A
  assume nfcsb.2: |- F/_ x B


  assert |- F/_ x [_ A / y ]_ B

  proof
    vx
    vy
    cA
    cB
    csb
    wnfc
    wtru
    vx
    vy
    cA
    cB
    vy
    nftru
    vx
    cA
    wnfc
    wtru
    nfcsb.1
    a1i
    vx
    cB
    wnfc
    wtru
    nfcsb.2
    a1i
    nfcsbd
    trud
end
