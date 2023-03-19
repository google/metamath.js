include "ccld.mm"
include "cfv.mm"
include "cin.mm"
include "wcel.mm"
include "wa.mm"
include "ctop.mm"
include "wss.mm"
include "cv.mm"
include "wb.mm"
include "wral.mm"
include "wrex.mm"
include "elin.mm"
include "cdif.mm"
include "iscld2.mm"
include "anbi2d.mm"
include "eltop2.mm"
include "dfss3.mm"
include "pm5.501.mm"
include "ralbidv.mm"
include "syl5bb.mm"
include "rexbidv.mm"
include "ralbiia.mm"
include "syl6bb.mm"
include "wn.mm"
include "cuni.mm"
include "id.mm"
include "simpr.mm"
include "elunii.mm"
include "syl2anr.mm"
include "syl6eleqr.mm"
include "eldif.mm"
include "baib.mm"
include "syl.mm"
include "eldifn.mm"
include "nbn2.mm"
include "ad2antrr.mm"
include "bitrd.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "anbi12d.mm"
include "adantr.mm"
include "cun.mm"
include "ralunb.mm"
include "wceq.mm"
include "undif.mm"
include "sylib.mm"
include "raleqdv.mm"
include "syl5bbr.mm"
include "3bitrd.mm"

theorem isclo
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cJ: class J
  let cX: class X
  let vw: setvar w
  assume isclo.1: |- X = U. J

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  assert |- ( ( J e. Top /\ A C_ X ) -> ( A e. ( J i^i ( Clsd ` J ) ) <-> A. x e. X E. y e. J ( x e. y /\ A. z e. y ( x e. A <-> z e. A ) ) ) )

  proof
    cA
    cJ
    cJ
    ccld
    cfv
    #
    cin
    wcel
    cA
    cJ
    wcel
    #
    cA
    @0
    wcel
    #
    wa
    #
    cJ
    ctop
    wcel
    #
    cA
    cX
    wss
    #
    wa
    #
    vx
    cv
    #
    vy
    cv
    #
    wcel
    #
    @7
    cA
    wcel
    #
    vz
    cv
    #
    cA
    wcel
    #
    wb
    #
    vz
    @8
    wral
    #
    wa
    #
    vy
    cJ
    wrex
    #
    vx
    cX
    wral
    #
    cA
    cJ
    @0
    elin
    @6
    @3
    @1
    cX
    cA
    cdif
    #
    cJ
    wcel
    #
    wa
    #
    @16
    vx
    cA
    wral
    #
    @16
    vx
    @18
    wral
    #
    wa
    #
    @17
    @6
    @2
    @19
    @1
    cA
    cJ
    cX
    isclo.1
    iscld2
    anbi2d
    @4
    @20
    @23
    wb
    @5
    @4
    @1
    @21
    @19
    @22
    @4
    @1
    @9
    @8
    cA
    wss
    #
    wa
    #
    vy
    cJ
    wrex
    #
    vx
    cA
    wral
    @21
    vx
    vy
    cA
    cJ
    eltop2
    @26
    @16
    vx
    cA
    @10
    @25
    @15
    vy
    cJ
    @10
    @24
    @14
    @9
    @24
    @12
    vz
    @8
    wral
    @10
    @14
    vz
    @8
    cA
    dfss3
    @10
    @12
    @13
    vz
    @8
    @10
    @12
    pm5.501
    ralbidv
    syl5bb
    anbi2d
    rexbidv
    ralbiia
    syl6bb
    @4
    @19
    @9
    @8
    @18
    wss
    #
    wa
    #
    vy
    cJ
    wrex
    #
    vx
    @18
    wral
    @22
    vx
    vy
    @18
    cJ
    eltop2
    @29
    @16
    vx
    @18
    @7
    @18
    wcel
    #
    @28
    @15
    vy
    cJ
    @30
    @8
    cJ
    wcel
    #
    wa
    #
    @27
    @14
    @9
    @27
    @11
    @18
    wcel
    #
    vz
    @8
    wral
    @32
    @14
    vz
    @8
    @18
    dfss3
    @32
    @33
    @13
    vz
    @8
    @32
    @11
    @8
    wcel
    #
    wa
    #
    @33
    @12
    wn
    #
    @13
    @35
    @11
    cX
    wcel
    #
    @33
    @36
    wb
    @35
    @11
    cJ
    cuni
    #
    cX
    @34
    @34
    @31
    @11
    @38
    wcel
    @32
    @34
    id
    @30
    @31
    simpr
    @11
    @8
    cJ
    elunii
    syl2anr
    isclo.1
    syl6eleqr
    @33
    @37
    @36
    @11
    cX
    cA
    eldif
    baib
    syl
    @30
    @36
    @13
    wb
    #
    @31
    @34
    @30
    @10
    wn
    @39
    @7
    cX
    cA
    eldifn
    @10
    @12
    nbn2
    syl
    ad2antrr
    bitrd
    ralbidva
    syl5bb
    anbi2d
    rexbidva
    ralbiia
    syl6bb
    anbi12d
    adantr
    @23
    @16
    vx
    cA
    @18
    cun
    #
    wral
    @6
    @17
    @16
    vx
    cA
    @18
    ralunb
    @6
    @16
    vx
    @40
    cX
    @6
    @5
    @40
    cX
    wceq
    @4
    @5
    simpr
    cA
    cX
    undif
    sylib
    raleqdv
    syl5bbr
    3bitrd
    syl5bb
end
