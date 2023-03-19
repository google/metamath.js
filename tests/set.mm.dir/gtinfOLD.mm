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
include "clt.mm"
include "ccnv.mm"
include "csup.mm"
include "wa.mm"
include "simprl.mm"
include "cvv.mm"
include "wb.mm"
include "gtso.mm"
include "supex.mm"
include "brcnvg.mm"
include "mpan2.mm"
include "biimpar.mm"
include "adantl.mm"
include "wor.mm"
include "a1i.mm"
include "wn.mm"
include "wi.mm"
include "infm3.mm"
include "vex.mm"
include "brcnv.mm"
include "notbii.mm"
include "ralbii.mm"
include "rexbii.mm"
include "imbi12i.mm"
include "anbi12i.mm"
include "sylibr.mm"
include "adantr.mm"
include "suplub.mm"
include "mp2and.mm"
include "rexbidv.mm"
include "ad2antrl.mm"
include "mpbid.mm"

theorem gtinfOLD
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cS: class S

  disjoint A z
  disjoint x y
  disjoint x z
  disjoint S x
  disjoint y z
  disjoint S y
  disjoint S z
  assert |- ( ( ( S C_ RR /\ S =/= (/) /\ E. x e. RR A. y e. S x <_ y ) /\ ( A e. RR /\ sup ( S , RR , `' < ) < A ) ) -> E. z e. S z < A )

  proof
    cS
    cr
    wss
    cS
    c0
    wne
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    vy
    cS
    wral
    vx
    cr
    wrex
    w3a
    #
    cA
    cr
    wcel
    #
    cS
    cr
    clt
    ccnv
    #
    csup
    #
    cA
    clt
    wbr
    #
    wa
    #
    wa
    #
    cA
    vz
    cv
    #
    @4
    wbr
    #
    vz
    cS
    wrex
    #
    @9
    cA
    clt
    wbr
    #
    vz
    cS
    wrex
    #
    @8
    @3
    cA
    @5
    @4
    wbr
    #
    @11
    @2
    @3
    @6
    simprl
    @7
    @14
    @2
    @3
    @14
    @6
    @3
    @5
    cvv
    wcel
    @14
    @6
    wb
    cr
    cS
    @4
    gtso
    supex
    cA
    @5
    cr
    cvv
    clt
    brcnvg
    mpan2
    biimpar
    adantl
    @8
    vx
    vy
    vz
    cr
    cS
    cA
    @4
    cr
    @4
    wor
    @8
    gtso
    a1i
    @2
    @0
    @1
    @4
    wbr
    #
    wn
    #
    vy
    cS
    wral
    #
    @1
    @0
    @4
    wbr
    #
    @1
    @9
    @4
    wbr
    #
    vz
    cS
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
    wrex
    #
    @7
    @2
    @1
    @0
    clt
    wbr
    #
    wn
    #
    vy
    cS
    wral
    #
    @0
    @1
    clt
    wbr
    #
    @9
    @1
    clt
    wbr
    #
    vz
    cS
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
    wrex
    @24
    vx
    vy
    vz
    cS
    infm3
    @23
    @33
    vx
    cr
    @17
    @27
    @22
    @32
    @16
    @26
    vy
    cS
    @15
    @25
    @0
    @1
    clt
    vx
    vex
    #
    vy
    vex
    #
    brcnv
    notbii
    ralbii
    @21
    @31
    vy
    cr
    @18
    @28
    @20
    @30
    @1
    @0
    clt
    @35
    @34
    brcnv
    @19
    @29
    vz
    cS
    @1
    @9
    clt
    @35
    vz
    vex
    #
    brcnv
    rexbii
    imbi12i
    ralbii
    anbi12i
    rexbii
    sylibr
    adantr
    suplub
    mp2and
    @3
    @11
    @13
    wb
    @2
    @6
    @3
    @10
    @12
    vz
    cS
    @3
    @9
    cvv
    wcel
    @10
    @12
    wb
    @36
    cA
    @9
    cr
    cvv
    clt
    brcnvg
    mpan2
    rexbidv
    ad2antrl
    mpbid
end
