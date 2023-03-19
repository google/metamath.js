include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "cph.mm"
include "cin.mm"
include "simplll.mm"
include "simpllr.mm"
include "cmv.mm"
include "chil.mm"
include "3oalem1.mm"
include "hvaddsub12.mm"
include "3anidm23.mm"
include "c0v.mm"
include "hvsubid.mm"
include "oveq2d.mm"
include "ax-hvaddid.mm"
include "sylan9eqr.mm"
include "eqtr3d.mm"
include "ad2ant2l.mm"
include "adantlr.mm"
include "syl.mm"
include "simprlr.mm"
include "eqtr2.mm"
include "oveq1d.mm"
include "simpl.mm"
include "anim1i.mm"
include "hvsub4.mm"
include "syldan.mm"
include "ad2antrr.mm"
include "hvsubcl.mm"
include "hvaddid2.mm"
include "adantll.mm"
include "3eqtrd.mm"
include "ad2ant2rl.mm"
include "simpr.mm"
include "anim2i.mm"
include "syl2anc.mm"
include "ad2antll.mm"
include "ancoms.mm"
include "adantrr.mm"
include "3eqtr3d.mm"
include "simpll.mm"
include "chshii.mm"
include "shsvsi.mm"
include "shscomi.mm"
include "syl6eleqr.mm"
include "syl2an.mm"
include "eqeltrd.mm"
include "simplr.mm"
include "elind.mm"
include "shscli.mm"
include "shincli.mm"
include "shsvai.mm"
include "eqeltrrd.mm"
include "wb.mm"
include "eleq1.mm"
include "ad2antlr.mm"
include "mpbird.mm"

theorem 3oalem2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  assume 3oalem1.1: |- B e. CH
  assume 3oalem1.2: |- C e. CH
  assume 3oalem1.3: |- R e. CH
  assume 3oalem1.4: |- S e. CH

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint B x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint B y
  disjoint w z
  disjoint v z
  disjoint B z
  disjoint v w
  disjoint B w
  disjoint B v
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint C w
  disjoint C v
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint R w
  disjoint R v
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint S w
  disjoint S v
  assert |- ( ( ( ( x e. B /\ y e. R ) /\ v = ( x +h y ) ) /\ ( ( z e. C /\ w e. S ) /\ v = ( z +h w ) ) ) -> v e. ( B +H ( R i^i ( S +H ( ( B +H C ) i^i ( R +H S ) ) ) ) ) )

  proof
    vx
    cv
    #
    cB
    wcel
    #
    vy
    cv
    #
    cR
    wcel
    #
    wa
    #
    vv
    cv
    #
    @0
    @2
    cva
    co
    #
    wceq
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
    cS
    wcel
    #
    wa
    #
    @5
    @9
    @11
    cva
    co
    #
    wceq
    #
    wa
    #
    wa
    #
    @5
    cB
    cR
    cS
    cB
    cC
    cph
    co
    #
    cR
    cS
    cph
    co
    #
    cin
    #
    cph
    co
    #
    cin
    #
    cph
    co
    #
    wcel
    #
    @6
    @23
    wcel
    #
    @17
    @1
    @2
    @22
    wcel
    @25
    @1
    @3
    @7
    @16
    simplll
    @17
    cR
    @21
    @2
    @1
    @3
    @7
    @16
    simpllr
    @17
    @11
    @2
    @11
    cmv
    co
    #
    cva
    co
    #
    @2
    @21
    @17
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
    wa
    @9
    chil
    wcel
    #
    @11
    chil
    wcel
    #
    wa
    #
    wa
    #
    @27
    @2
    wceq
    #
    vx
    vy
    vz
    vw
    vv
    cB
    cC
    cR
    cS
    3oalem1.1
    3oalem1.2
    3oalem1.3
    3oalem1.4
    3oalem1
    #
    @30
    @34
    @36
    @31
    @29
    @33
    @36
    @28
    @32
    @29
    @33
    wa
    #
    @2
    @11
    @11
    cmv
    co
    #
    cva
    co
    #
    @27
    @2
    @29
    @33
    @40
    @27
    wceq
    @2
    @11
    @11
    hvaddsub12
    3anidm23
    @33
    @29
    @40
    @2
    c0v
    cva
    co
    @2
    @33
    @39
    c0v
    @2
    cva
    @11
    hvsubid
    #
    oveq2d
    @2
    ax-hvaddid
    sylan9eqr
    eqtr3d
    ad2ant2l
    adantlr
    syl
    @17
    @12
    @26
    @20
    wcel
    @27
    @21
    wcel
    @8
    @10
    @12
    @15
    simprlr
    @17
    @18
    @19
    @26
    @17
    @26
    @9
    @0
    cmv
    co
    #
    @18
    @17
    @6
    @0
    @11
    cva
    co
    #
    cmv
    co
    #
    @14
    @43
    cmv
    co
    #
    @26
    @42
    @7
    @15
    @44
    @45
    wceq
    @4
    @13
    @7
    @15
    wa
    @6
    @14
    @43
    cmv
    @5
    @6
    @14
    eqtr2
    oveq1d
    ad2ant2l
    @17
    @35
    @44
    @26
    wceq
    #
    @37
    @30
    @33
    @46
    @31
    @32
    @30
    @33
    wa
    #
    @44
    @0
    @0
    cmv
    co
    #
    @26
    cva
    co
    #
    c0v
    @26
    cva
    co
    #
    @26
    @30
    @33
    @28
    @33
    wa
    #
    @44
    @49
    wceq
    @30
    @28
    @33
    @28
    @29
    simpl
    anim1i
    @0
    @2
    @0
    @11
    hvsub4
    syldan
    @47
    @48
    c0v
    @26
    cva
    @28
    @48
    c0v
    wceq
    @29
    @33
    @0
    hvsubid
    ad2antrr
    oveq1d
    @29
    @33
    @50
    @26
    wceq
    #
    @28
    @38
    @26
    chil
    wcel
    @52
    @2
    @11
    hvsubcl
    @26
    hvaddid2
    syl
    adantll
    3eqtrd
    ad2ant2rl
    syl
    @17
    @35
    @45
    @42
    wceq
    #
    @37
    @30
    @34
    @53
    @31
    @28
    @34
    @53
    @29
    @28
    @34
    wa
    #
    @45
    @42
    @39
    cva
    co
    #
    @42
    c0v
    cva
    co
    #
    @42
    @54
    @34
    @51
    @45
    @55
    wceq
    @28
    @34
    simpr
    @34
    @33
    @28
    @32
    @33
    simpr
    anim2i
    @9
    @11
    @0
    @11
    hvsub4
    syl2anc
    @54
    @39
    c0v
    @42
    cva
    @33
    @39
    c0v
    wceq
    @28
    @32
    @41
    ad2antll
    oveq2d
    @28
    @32
    @56
    @42
    wceq
    #
    @33
    @32
    @28
    @57
    @32
    @28
    wa
    @42
    chil
    wcel
    @57
    @9
    @0
    hvsubcl
    @42
    ax-hvaddid
    syl
    ancoms
    adantrr
    3eqtrd
    adantlr
    adantlr
    syl
    3eqtr3d
    @8
    @1
    @10
    @42
    @18
    wcel
    @16
    @1
    @3
    @7
    simpll
    @10
    @12
    @15
    simpll
    @1
    @10
    wa
    @42
    cC
    cB
    cph
    co
    #
    @18
    @10
    @1
    @42
    @58
    wcel
    cC
    cB
    @9
    @0
    cC
    3oalem1.2
    chshii
    #
    cB
    3oalem1.1
    chshii
    #
    shsvsi
    ancoms
    cB
    cC
    @60
    @59
    shscomi
    syl6eleqr
    syl2an
    eqeltrd
    @8
    @3
    @12
    @26
    @19
    wcel
    @16
    @1
    @3
    @7
    simplr
    @10
    @12
    @15
    simplr
    cR
    cS
    @2
    @11
    cR
    3oalem1.3
    chshii
    #
    cS
    3oalem1.4
    chshii
    #
    shsvsi
    syl2an
    elind
    cS
    @20
    @11
    @26
    @62
    @18
    @19
    cB
    cC
    @60
    @59
    shscli
    cR
    cS
    @61
    @62
    shscli
    shincli
    #
    shsvai
    syl2anc
    eqeltrrd
    elind
    cB
    @22
    @0
    @2
    @60
    cR
    @21
    @61
    cS
    @20
    @62
    @63
    shscli
    shincli
    shsvai
    syl2anc
    @7
    @24
    @25
    wb
    @4
    @16
    @5
    @6
    @23
    eleq1
    ad2antlr
    mpbird
end
