include "wnfc.mm"
include "nfceqi.mm"
include "mpbir.mm"

theorem nfcxfr
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume nfceqi.1: |- A = B
  assume nfcxfr.2: |- F/_ x B


  assert |- F/_ x A

  proof
    vx
    cA
    wnfc
    vx
    cB
    wnfc
    nfcxfr.2
    vx
    cA
    cB
    nfceqi.1
    nfceqi
    mpbir
end
