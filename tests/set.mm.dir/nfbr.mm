include "wbr.mm"
include "wnf.mm"
include "wtru.mm"
include "wnfc.mm"
include "a1i.mm"
include "nfbrd.mm"
include "trud.mm"

theorem nfbr
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  assume nfbr.1: |- F/_ x A
  assume nfbr.2: |- F/_ x R
  assume nfbr.3: |- F/_ x B


  assert |- F/ x A R B

  proof
    cA
    cB
    cR
    wbr
    vx
    wnf
    wtru
    vx
    cA
    cB
    cR
    vx
    cA
    wnfc
    wtru
    nfbr.1
    a1i
    vx
    cR
    wnfc
    wtru
    nfbr.2
    a1i
    vx
    cB
    wnfc
    wtru
    nfbr.3
    a1i
    nfbrd
    trud
end
