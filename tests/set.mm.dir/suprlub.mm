include "cr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "w3a.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "csup.mm"
include "wor.mm"
include "ltso.mm"
include "a1i.mm"
include "sup3.mm"
include "simp1.mm"
include "suplub2.mm"
include "breq2.mm"
include "cbvrexv.mm"
include "syl6bb.mm"

theorem suprlub
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vw: setvar w

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint A z
  disjoint B z
  disjoint A w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  assert |- ( ( ( A C_ RR /\ A =/= (/) /\ E. x e. RR A. y e. A y <_ x ) /\ B e. RR ) -> ( B < sup ( A , RR , < ) <-> E. z e. A B < z ) )

  proof
    cA
    cr
    wss
    #
    cA
    c0
    wne
    #
    vy
    cv
    vx
    cv
    cle
    wbr
    vy
    cA
    wral
    vx
    cr
    wrex
    #
    w3a
    #
    cB
    cr
    wcel
    wa
    cB
    cA
    cr
    clt
    csup
    clt
    wbr
    cB
    vw
    cv
    #
    clt
    wbr
    #
    vw
    cA
    wrex
    cB
    vz
    cv
    #
    clt
    wbr
    #
    vz
    cA
    wrex
    @3
    vx
    vy
    vw
    cr
    cA
    cB
    clt
    cr
    clt
    wor
    @3
    ltso
    a1i
    vx
    vy
    vw
    cA
    sup3
    @0
    @1
    @2
    simp1
    suplub2
    @5
    @7
    vw
    vz
    cA
    @4
    @6
    cB
    clt
    breq2
    cbvrexv
    syl6bb
end
