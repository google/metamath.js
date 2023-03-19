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
include "wn.mm"
include "suprnub.mm"
include "wb.mm"
include "suprcl.mm"
include "lenlt.mm"
include "sylan.mm"
include "simpl1.mm"
include "sselda.mm"
include "simplr.mm"
include "lenltd.mm"
include "ralbidva.mm"
include "3bitr4d.mm"
include "breq1.mm"
include "cbvralv.mm"
include "syl6bb.mm"

theorem suprleub
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
  assert |- ( ( ( A C_ RR /\ A =/= (/) /\ E. x e. RR A. y e. A y <_ x ) /\ B e. RR ) -> ( sup ( A , RR , < ) <_ B <-> A. z e. A z <_ B ) )

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
    #
    wa
    #
    cA
    cr
    clt
    csup
    #
    cB
    cle
    wbr
    #
    vw
    cv
    #
    cB
    cle
    wbr
    #
    vw
    cA
    wral
    #
    vz
    cv
    #
    cB
    cle
    wbr
    #
    vz
    cA
    wral
    @5
    cB
    @6
    clt
    wbr
    wn
    #
    cB
    @8
    clt
    wbr
    wn
    #
    vw
    cA
    wral
    @7
    @10
    vx
    vy
    vw
    cA
    cB
    suprnub
    @3
    @6
    cr
    wcel
    @4
    @7
    @13
    wb
    vx
    vy
    cA
    suprcl
    @6
    cB
    lenlt
    sylan
    @5
    @9
    @14
    vw
    cA
    @5
    @8
    cA
    wcel
    #
    wa
    @8
    cB
    @5
    cA
    cr
    @8
    @0
    @1
    @2
    @4
    simpl1
    sselda
    @3
    @4
    @15
    simplr
    lenltd
    ralbidva
    3bitr4d
    @9
    @12
    vw
    vz
    cA
    @8
    @11
    cB
    cle
    breq1
    cbvralv
    syl6bb
end
