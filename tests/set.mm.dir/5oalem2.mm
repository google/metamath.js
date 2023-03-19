include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "cph.mm"
include "cmv.mm"
include "shsvsi.mm"
include "ad2ant2r.mm"
include "adantr.mm"
include "ancoms.mm"
include "shscomi.mm"
include "syl6eleqr.mm"
include "ad2ant2l.mm"
include "chil.mm"
include "wb.mm"
include "sheli.mm"
include "anim12i.mm"
include "oveq1.mm"
include "adantl.mm"
include "c0v.mm"
include "simpr.mm"
include "anim2i.mm"
include "hvsub4.mm"
include "syldan.mm"
include "hvsubid.mm"
include "oveq2d.mm"
include "ad2antlr.mm"
include "hvsubcl.mm"
include "ax-hvaddid.mm"
include "syl.mm"
include "adantlr.mm"
include "3eqtrd.mm"
include "adantrr.mm"
include "simpl.mm"
include "anim1i.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "ad2antrl.mm"
include "hvaddid2.mm"
include "adantrl.mm"
include "adantll.mm"
include "3eqtr3d.mm"
include "eleq1d.mm"
include "sylan.mm"
include "mpbird.mm"
include "elind.mm"

theorem 5oalem2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 5oalem2.1: |- A e. SH
  assume 5oalem2.2: |- B e. SH
  assume 5oalem2.3: |- C e. SH
  assume 5oalem2.4: |- D e. SH


  assert |- ( ( ( ( x e. A /\ y e. B ) /\ ( z e. C /\ w e. D ) ) /\ ( x +h y ) = ( z +h w ) ) -> ( x -h z ) e. ( ( A +H C ) i^i ( B +H D ) ) )

  proof
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    #
    vz
    cv
    #
    cC
    wcel
    #
    vw
    cv
    #
    cD
    wcel
    #
    wa
    #
    wa
    #
    @0
    @2
    cva
    co
    #
    @5
    @7
    cva
    co
    #
    wceq
    #
    wa
    #
    cA
    cC
    cph
    co
    #
    cB
    cD
    cph
    co
    #
    @0
    @5
    cmv
    co
    #
    @10
    @17
    @15
    wcel
    #
    @13
    @1
    @6
    @18
    @3
    @8
    cA
    cC
    @0
    @5
    5oalem2.1
    5oalem2.3
    shsvsi
    ad2ant2r
    adantr
    @14
    @17
    @16
    wcel
    #
    @7
    @2
    cmv
    co
    #
    @16
    wcel
    #
    @10
    @21
    @13
    @3
    @8
    @21
    @1
    @6
    @3
    @8
    wa
    @20
    cD
    cB
    cph
    co
    #
    @16
    @8
    @3
    @20
    @22
    wcel
    cD
    cB
    @7
    @2
    5oalem2.4
    5oalem2.2
    shsvsi
    ancoms
    cB
    cD
    5oalem2.2
    5oalem2.4
    shscomi
    syl6eleqr
    ad2ant2l
    adantr
    @10
    @0
    chil
    wcel
    #
    @2
    chil
    wcel
    #
    wa
    #
    @5
    chil
    wcel
    #
    @7
    chil
    wcel
    #
    wa
    #
    wa
    #
    @13
    @19
    @21
    wb
    @4
    @25
    @9
    @28
    @1
    @23
    @3
    @24
    @0
    cA
    5oalem2.1
    sheli
    @2
    cB
    5oalem2.2
    sheli
    anim12i
    @6
    @26
    @8
    @27
    @5
    cC
    5oalem2.3
    sheli
    @7
    cD
    5oalem2.4
    sheli
    anim12i
    anim12i
    @29
    @13
    wa
    #
    @17
    @20
    @16
    @30
    @11
    @5
    @2
    cva
    co
    #
    cmv
    co
    #
    @12
    @31
    cmv
    co
    #
    @17
    @20
    @13
    @32
    @33
    wceq
    @29
    @11
    @12
    @31
    cmv
    oveq1
    adantl
    @29
    @32
    @17
    wceq
    #
    @13
    @25
    @26
    @34
    @27
    @25
    @26
    wa
    @32
    @17
    @2
    @2
    cmv
    co
    #
    cva
    co
    #
    @17
    c0v
    cva
    co
    #
    @17
    @25
    @26
    @26
    @24
    wa
    #
    @32
    @36
    wceq
    @26
    @25
    @38
    @25
    @24
    @26
    @23
    @24
    simpr
    anim2i
    ancoms
    @0
    @2
    @5
    @2
    hvsub4
    syldan
    @24
    @36
    @37
    wceq
    @23
    @26
    @24
    @35
    c0v
    @17
    cva
    @2
    hvsubid
    oveq2d
    ad2antlr
    @23
    @26
    @37
    @17
    wceq
    #
    @24
    @23
    @26
    wa
    @17
    chil
    wcel
    @39
    @0
    @5
    hvsubcl
    @17
    ax-hvaddid
    syl
    adantlr
    3eqtrd
    adantrr
    adantr
    @29
    @33
    @20
    wceq
    #
    @13
    @24
    @28
    @40
    @23
    @24
    @28
    wa
    #
    @33
    @5
    @5
    cmv
    co
    #
    @20
    cva
    co
    #
    c0v
    @20
    cva
    co
    #
    @20
    @41
    @28
    @38
    @33
    @43
    wceq
    @24
    @28
    simpr
    @28
    @24
    @38
    @28
    @26
    @24
    @26
    @27
    simpl
    anim1i
    ancoms
    @5
    @7
    @5
    @2
    hvsub4
    syl2anc
    @26
    @43
    @44
    wceq
    @24
    @27
    @26
    @42
    c0v
    @20
    cva
    @5
    hvsubid
    oveq1d
    ad2antrl
    @24
    @27
    @44
    @20
    wceq
    #
    @26
    @27
    @24
    @45
    @27
    @24
    wa
    @20
    chil
    wcel
    @45
    @7
    @2
    hvsubcl
    @20
    hvaddid2
    syl
    ancoms
    adantrl
    3eqtrd
    adantll
    adantr
    3eqtr3d
    eleq1d
    sylan
    mpbird
    elind
end
