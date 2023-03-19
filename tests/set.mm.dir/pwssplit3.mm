include "clmod.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cvsca.mm"
include "cfv.mm"
include "csca.mm"
include "cbs.mm"
include "eqid.mm"
include "simp1.mm"
include "simp2.mm"
include "pwslmod.mm"
include "syl2anc.mm"
include "cvv.mm"
include "simp3.mm"
include "ssexd.mm"
include "wceq.mm"
include "pwssca.mm"
include "eqtr3d.mm"
include "cgrp.mm"
include "cghm.mm"
include "co.mm"
include "lmodgrp.mm"
include "pwssplit2.mm"
include "syl3an1.mm"
include "cv.mm"
include "wa.mm"
include "cres.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "snex.mm"
include "xpexg.mm"
include "sylancl.mm"
include "vex.mm"
include "offres.mm"
include "adantr.mm"
include "xpssres.mm"
include "3ad2ant3.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "simpl1.mm"
include "simpl2.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "adantrr.mm"
include "simprr.mm"
include "pwsvscafval.mm"
include "reseq1d.mm"
include "fvtresfn.mm"
include "ad2antll.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "lmodvscl.mm"
include "3expb.mm"
include "sylan.mm"
include "syl.mm"
include "pwssplit0.mm"
include "ffvelrnda.mm"
include "adantrl.mm"
include "islmhmd.mm"

theorem pwssplit3
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cU: class U
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let cT: class T
  assume pwssplit1.y: |- Y = ( W ^s U )
  assume pwssplit1.z: |- Z = ( W ^s V )
  assume pwssplit1.b: |- B = ( Base ` Y )
  assume pwssplit1.c: |- C = ( Base ` Z )
  assume pwssplit1.f: |- F = ( x e. B |-> ( x |` V ) )

  disjoint Y x
  disjoint W x
  disjoint U x
  disjoint Z x
  disjoint V x
  disjoint B x
  disjoint C x
  disjoint X x
  disjoint Y a
  disjoint Y b
  disjoint a b
  disjoint a x
  disjoint b x
  disjoint W a
  disjoint W b
  disjoint U a
  disjoint U b
  disjoint Z a
  disjoint Z b
  disjoint V a
  disjoint V b
  disjoint B a
  disjoint B b
  disjoint C a
  disjoint C b
  disjoint F a
  disjoint F b
  disjoint X a
  disjoint X b
  disjoint T x
  assert |- ( ( W e. LMod /\ U e. X /\ V C_ U ) -> F e. ( Y LMHom Z ) )

  proof
    cW
    clmod
    wcel
    #
    cU
    cX
    wcel
    #
    cV
    cU
    wss
    #
    w3a
    #
    va
    vb
    cY
    cZ
    cY
    cvsca
    cfv
    #
    cZ
    cvsca
    cfv
    #
    cF
    cZ
    csca
    cfv
    #
    cY
    csca
    cfv
    #
    @7
    cbs
    cfv
    #
    cB
    pwssplit1.b
    @4
    eqid
    #
    @5
    eqid
    #
    @7
    eqid
    #
    @6
    eqid
    @8
    eqid
    #
    @3
    @0
    @1
    cY
    clmod
    wcel
    #
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @2
    simp2
    #
    cW
    cU
    cX
    cY
    pwssplit1.y
    pwslmod
    syl2anc
    #
    @3
    @0
    cV
    cvv
    wcel
    #
    cZ
    clmod
    wcel
    @14
    @3
    cV
    cU
    cX
    @15
    @0
    @1
    @2
    simp3
    ssexd
    #
    cW
    cV
    cvv
    cZ
    pwssplit1.z
    pwslmod
    syl2anc
    @3
    cW
    csca
    cfv
    #
    @6
    @7
    @3
    @0
    @17
    @19
    @6
    wceq
    @14
    @18
    cW
    @19
    cV
    clmod
    cvv
    cZ
    pwssplit1.z
    @19
    eqid
    #
    pwssca
    syl2anc
    @3
    @0
    @1
    @19
    @7
    wceq
    @14
    @15
    cW
    @19
    cU
    clmod
    cX
    cY
    pwssplit1.y
    @20
    pwssca
    syl2anc
    #
    eqtr3d
    @0
    cW
    cgrp
    wcel
    @1
    @2
    cF
    cY
    cZ
    cghm
    co
    wcel
    cW
    lmodgrp
    vx
    cB
    cC
    cU
    cF
    cV
    cW
    cX
    cY
    cZ
    pwssplit1.y
    pwssplit1.z
    pwssplit1.b
    pwssplit1.c
    pwssplit1.f
    pwssplit2
    syl3an1
    @3
    va
    cv
    #
    @8
    wcel
    #
    vb
    cv
    #
    cB
    wcel
    #
    wa
    #
    wa
    #
    @22
    @24
    @4
    co
    #
    cV
    cres
    #
    cV
    @22
    csn
    #
    cxp
    #
    @24
    cF
    cfv
    #
    cW
    cvsca
    cfv
    #
    cof
    #
    co
    #
    @28
    cF
    cfv
    #
    @22
    @32
    @5
    co
    @27
    cU
    @30
    cxp
    #
    @24
    @34
    co
    #
    cV
    cres
    #
    @31
    @24
    cV
    cres
    #
    @34
    co
    #
    @29
    @35
    @27
    @39
    @37
    cV
    cres
    #
    @40
    @34
    co
    #
    @41
    @3
    @39
    @43
    wceq
    #
    @26
    @3
    @37
    cvv
    wcel
    #
    @24
    cvv
    wcel
    @44
    @3
    @1
    @30
    cvv
    wcel
    @45
    @15
    @22
    snex
    cU
    @30
    cX
    cvv
    xpexg
    sylancl
    vb
    vex
    cV
    @33
    @37
    @24
    cvv
    cvv
    offres
    sylancl
    adantr
    @27
    @42
    @31
    @40
    @34
    @3
    @42
    @31
    wceq
    #
    @26
    @2
    @0
    @46
    @1
    cU
    @30
    cV
    xpssres
    3ad2ant3
    adantr
    oveq1d
    eqtrd
    @27
    @28
    @38
    cV
    @27
    @22
    cB
    cW
    @4
    @33
    @19
    cU
    @19
    cbs
    cfv
    #
    clmod
    cX
    @24
    cY
    pwssplit1.y
    pwssplit1.b
    @33
    eqid
    #
    @9
    @20
    @47
    eqid
    #
    @0
    @1
    @2
    @26
    simpl1
    #
    @0
    @1
    @2
    @26
    simpl2
    @3
    @23
    @22
    @47
    wcel
    #
    @25
    @3
    @51
    @23
    @3
    @47
    @8
    @22
    @3
    @19
    @7
    cbs
    @21
    fveq2d
    eleq2d
    biimpar
    adantrr
    #
    @3
    @23
    @25
    simprr
    pwsvscafval
    reseq1d
    @27
    @32
    @40
    @31
    @34
    @25
    @32
    @40
    wceq
    @3
    @23
    vx
    cB
    cF
    cV
    @24
    pwssplit1.f
    fvtresfn
    ad2antll
    oveq2d
    3eqtr4d
    @27
    @28
    cB
    wcel
    #
    @36
    @29
    wceq
    @3
    @13
    @26
    @53
    @16
    @13
    @23
    @25
    @53
    @22
    @4
    @7
    @8
    cB
    cY
    @24
    pwssplit1.b
    @11
    @9
    @12
    lmodvscl
    3expb
    sylan
    vx
    cB
    cF
    cV
    @28
    pwssplit1.f
    fvtresfn
    syl
    @27
    @22
    cC
    cW
    @5
    @33
    @19
    cV
    @47
    clmod
    cvv
    @32
    cZ
    pwssplit1.z
    pwssplit1.c
    @48
    @10
    @20
    @49
    @50
    @3
    @17
    @26
    @18
    adantr
    @52
    @3
    @25
    @32
    cC
    wcel
    @23
    @3
    cB
    cC
    @24
    cF
    vx
    cB
    cC
    clmod
    cU
    cF
    cV
    cW
    cX
    cY
    cZ
    pwssplit1.y
    pwssplit1.z
    pwssplit1.b
    pwssplit1.c
    pwssplit1.f
    pwssplit0
    ffvelrnda
    adantrl
    pwsvscafval
    3eqtr4d
    islmhmd
end
