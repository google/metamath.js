include "cr.mm"
include "wss.mm"
include "clt.mm"
include "cinf.mm"
include "ccnv.mm"
include "csup.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "crab.mm"
include "cuni.mm"
include "df-inf.mm"
include "wn.mm"
include "df-sup.mm"
include "wcel.mm"
include "wb.mm"
include "ssel2.mm"
include "lenlt.mm"
include "vex.mm"
include "brcnv.mm"
include "notbii.mm"
include "syl6rbbr.mm"
include "sylan2.mm"
include "ancoms.mm"
include "an32s.mm"
include "ralbidva.mm"
include "rexbii.mm"
include "imbi12i.mm"
include "ralbii.mm"
include "a1i.mm"
include "anbi12d.mm"
include "rabbidva.mm"
include "unieqd.mm"
include "syl5eq.mm"

theorem dfinfre
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vw: setvar w

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A w
  disjoint w x
  disjoint w y
  disjoint w z
  assert |- ( A C_ RR -> inf ( A , RR , < ) = U. { x e. RR | ( A. y e. A x <_ y /\ A. y e. RR ( x < y -> E. z e. A z < y ) ) } )

  proof
    cA
    cr
    wss
    #
    cA
    cr
    clt
    cinf
    cA
    cr
    clt
    ccnv
    #
    csup
    #
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vy
    cA
    wral
    #
    @3
    @4
    clt
    wbr
    #
    vz
    cv
    #
    @4
    clt
    wbr
    #
    vz
    cA
    wrex
    #
    wi
    #
    vy
    cr
    wral
    #
    wa
    #
    vx
    cr
    crab
    #
    cuni
    #
    cA
    cr
    clt
    df-inf
    @0
    @2
    @3
    @4
    @1
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    @4
    @3
    @1
    wbr
    #
    @4
    @8
    @1
    wbr
    #
    vz
    cA
    wrex
    #
    wi
    #
    vy
    cr
    wral
    #
    wa
    #
    vx
    cr
    crab
    #
    cuni
    @15
    vx
    vy
    vz
    cA
    cr
    @1
    df-sup
    @0
    @25
    @14
    @0
    @24
    @13
    vx
    cr
    @0
    @3
    cr
    wcel
    #
    wa
    #
    @18
    @6
    @23
    @12
    @27
    @17
    @5
    vy
    cA
    @0
    @4
    cA
    wcel
    #
    @26
    @17
    @5
    wb
    #
    @26
    @0
    @28
    wa
    #
    @29
    @30
    @26
    @4
    cr
    wcel
    #
    @29
    cA
    cr
    @4
    ssel2
    @26
    @31
    wa
    @5
    @4
    @3
    clt
    wbr
    #
    wn
    @17
    @3
    @4
    lenlt
    @16
    @32
    @3
    @4
    clt
    vx
    vex
    #
    vy
    vex
    #
    brcnv
    notbii
    syl6rbbr
    sylan2
    ancoms
    an32s
    ralbidva
    @23
    @12
    wb
    @27
    @22
    @11
    vy
    cr
    @19
    @7
    @21
    @10
    @4
    @3
    clt
    @34
    @33
    brcnv
    @20
    @9
    vz
    cA
    @4
    @8
    clt
    @34
    vz
    vex
    brcnv
    rexbii
    imbi12i
    ralbii
    a1i
    anbi12d
    rabbidva
    unieqd
    syl5eq
    syl5eq
end
