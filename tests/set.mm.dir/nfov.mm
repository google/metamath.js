include "co.mm"
include "wnfc.mm"
include "wtru.mm"
include "a1i.mm"
include "nfovd.mm"
include "trud.mm"

theorem nfov
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  assume nfov.1: |- F/_ x A
  assume nfov.2: |- F/_ x F
  assume nfov.3: |- F/_ x B


  assert |- F/_ x ( A F B )

  proof
    vx
    cA
    cB
    cF
    co
    wnfc
    wtru
    vx
    cA
    cB
    cF
    vx
    cA
    wnfc
    wtru
    nfov.1
    a1i
    vx
    cF
    wnfc
    wtru
    nfov.2
    a1i
    vx
    cB
    wnfc
    wtru
    nfov.3
    a1i
    nfovd
    trud
end
