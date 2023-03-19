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
include "cinf.mm"
include "wn.mm"
include "wor.mm"
include "ltso.mm"
include "a1i.mm"
include "infm3.mm"
include "simp1.mm"
include "infglbb.mm"
include "notbid.mm"
include "wb.mm"
include "infrecl.mm"
include "anim1i.mm"
include "ancomd.mm"
include "lenlt.mm"
include "syl.mm"
include "simplr.mm"
include "wi.mm"
include "ssel.mm"
include "adantr.mm"
include "imp.mm"
include "lenltd.mm"
include "ralbidva.mm"
include "3ad2antl1.mm"
include "ralnex.mm"
include "syl6bb.mm"
include "3bitr4d.mm"
include "breq2.mm"
include "cbvralv.mm"

theorem infregelb
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vw: setvar w

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B z
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint w z
  disjoint B w
  assert |- ( ( ( A C_ RR /\ A =/= (/) /\ E. x e. RR A. y e. A x <_ y ) /\ B e. RR ) -> ( B <_ inf ( A , RR , < ) <-> A. z e. A B <_ z ) )

  proof
    cA
    cr
    wss
    #
    cA
    c0
    wne
    #
    vx
    cv
    vy
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
    cB
    cA
    cr
    clt
    cinf
    #
    cle
    wbr
    #
    cB
    vw
    cv
    #
    cle
    wbr
    #
    vw
    cA
    wral
    #
    cB
    vz
    cv
    #
    cle
    wbr
    #
    vz
    cA
    wral
    @5
    @6
    cB
    clt
    wbr
    #
    wn
    #
    @8
    cB
    clt
    wbr
    #
    vw
    cA
    wrex
    #
    wn
    #
    @7
    @10
    @5
    @13
    @16
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
    infm3
    @0
    @1
    @2
    simp1
    infglbb
    notbid
    @5
    @4
    @6
    cr
    wcel
    #
    wa
    @7
    @14
    wb
    @5
    @18
    @4
    @3
    @18
    @4
    vx
    vy
    cA
    infrecl
    anim1i
    ancomd
    cB
    @6
    lenlt
    syl
    @5
    @10
    @15
    wn
    #
    vw
    cA
    wral
    #
    @17
    @0
    @1
    @4
    @10
    @20
    wb
    @2
    @0
    @4
    wa
    #
    @9
    @19
    vw
    cA
    @21
    @8
    cA
    wcel
    #
    wa
    cB
    @8
    @0
    @4
    @22
    simplr
    @21
    @22
    @8
    cr
    wcel
    #
    @0
    @22
    @23
    wi
    @4
    cA
    cr
    @8
    ssel
    adantr
    imp
    lenltd
    ralbidva
    3ad2antl1
    @15
    vw
    cA
    ralnex
    syl6bb
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
    breq2
    cbvralv
    syl6bb
end
