include "ccrg.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "cif.mm"
include "cbs.mm"
include "eqid.mm"
include "simpl.mm"
include "3ad2ant1.mm"
include "cfn.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "adantr.mm"
include "3ad2ant2.mm"
include "cxp.mm"
include "cmap.mm"
include "wi.mm"
include "anim2i.mm"
include "ancomd.mm"
include "matbas2.mm"
include "syl.mm"
include "syl6reqr.mm"
include "eleq2d.mm"
include "biimpd.mm"
include "ex.mm"
include "com12.mm"
include "pm2.43a.mm"
include "impcom.mm"
include "3adant3.mm"
include "crg.mm"
include "crngring.mm"
include "anim12i.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "adantl.mm"
include "3jca.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "simp3.mm"
include "mavmulsolcl.mm"
include "imp.mm"
include "syl21anc.mm"
include "simpr.mm"
include "cur.mm"
include "cmatrepV.mm"
include "ma1repvcl.mm"
include "syl5eqel.mm"
include "syl12anc.mm"
include "eqcomd.mm"
include "ad2ant2r.mm"
include "eleqtrrd.mm"
include "mamuval.mm"
include "simp2.mm"
include "c0g.mm"
include "mulmarep1gsum2.mm"
include "syl113anc.mm"
include "mpt2eq3dva.mm"
include "marepvval.mm"
include "syl3anc.mm"
include "syl5req.mm"
include "3eqtrd.mm"

theorem cramerimplem2
  let cA: class A
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let cE: class E
  let cH: class H
  let cI: class I
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vl: setvar l
  let vi: setvar i
  let vj: setvar j
  assume cramerimp.a: |- A = ( N Mat R )
  assume cramerimp.b: |- B = ( Base ` A )
  assume cramerimp.v: |- V = ( ( Base ` R ) ^m N )
  assume cramerimp.e: |- E = ( ( ( 1r ` A ) ( N matRepV R ) Z ) ` I )
  assume cramerimp.h: |- H = ( ( X ( N matRepV R ) Y ) ` I )
  assume cramerimp.x: |- .x. = ( R maVecMul <. N , N >. )
  assume cramerimp.m: |- .X. = ( R maMul <. N , N , N >. )


  assert |- ( ( ( R e. CRing /\ I e. N ) /\ ( X e. B /\ Y e. V ) /\ ( X .x. Z ) = Y ) -> ( X .X. E ) = H )

  proof
    cR
    ccrg
    wcel
    #
    cI
    cN
    wcel
    #
    wa
    #
    cX
    cB
    wcel
    #
    cY
    cV
    wcel
    #
    wa
    #
    cX
    cZ
    c.x
    co
    cY
    wceq
    #
    w3a
    #
    cX
    cE
    c.xp
    co
    vi
    vj
    cN
    cN
    cR
    vl
    cN
    vi
    cv
    #
    vl
    cv
    #
    cX
    co
    @9
    vj
    cv
    #
    cE
    co
    cR
    cmulr
    cfv
    #
    co
    cmpt
    cgsu
    co
    #
    cmpt2
    vi
    vj
    cN
    cN
    @10
    cI
    wceq
    @8
    cY
    cfv
    @8
    @10
    cX
    co
    cif
    #
    cmpt2
    #
    cH
    @7
    cR
    cbs
    cfv
    #
    cN
    cR
    @11
    vi
    vl
    vj
    c.xp
    cN
    cN
    ccrg
    cX
    cE
    cramerimp.m
    @15
    eqid
    #
    @11
    eqid
    @2
    @5
    @0
    @6
    @0
    @1
    simpl
    #
    3ad2ant1
    @5
    @2
    cN
    cfn
    wcel
    #
    @6
    @3
    @18
    @4
    @3
    @18
    cR
    cvv
    wcel
    cA
    cB
    cR
    cN
    cX
    cramerimp.a
    cramerimp.b
    matrcl
    simpld
    #
    adantr
    #
    3ad2ant2
    #
    @21
    @21
    @2
    @5
    cX
    @15
    cN
    cN
    cxp
    cmap
    co
    #
    wcel
    #
    @6
    @5
    @2
    @23
    @3
    @2
    @23
    wi
    @4
    @2
    @3
    @23
    @2
    @3
    @3
    @23
    wi
    #
    @0
    @3
    @24
    wi
    @1
    @0
    @3
    @24
    @0
    @3
    wa
    #
    @3
    @23
    @25
    cB
    @22
    cX
    @25
    @22
    cA
    cbs
    cfv
    #
    cB
    @25
    @18
    @0
    wa
    @22
    @26
    wceq
    @25
    @0
    @18
    @3
    @18
    @0
    @19
    anim2i
    ancomd
    cA
    cR
    @15
    cN
    ccrg
    cramerimp.a
    @16
    matbas2
    syl
    cramerimp.b
    syl6reqr
    #
    eleq2d
    biimpd
    ex
    adantr
    com12
    pm2.43a
    adantr
    impcom
    3adant3
    @7
    cE
    cB
    @22
    @7
    cR
    crg
    wcel
    #
    @18
    wa
    #
    cZ
    cV
    wcel
    #
    @1
    cE
    cB
    wcel
    @2
    @5
    @29
    @6
    @2
    @28
    @5
    @18
    @0
    @28
    @1
    cR
    crngring
    adantr
    #
    @20
    anim12i
    3adant3
    @7
    @18
    @18
    cN
    c0
    wne
    #
    w3a
    #
    @0
    cY
    @15
    cN
    cmap
    co
    #
    wcel
    #
    wa
    #
    @6
    @30
    @7
    @18
    @18
    @32
    @21
    @21
    @2
    @5
    @32
    @6
    @1
    @32
    @0
    cN
    cI
    ne0i
    adantl
    3ad2ant1
    3jca
    @2
    @5
    @36
    @6
    @2
    @0
    @5
    @35
    @17
    @4
    @35
    @3
    @4
    @35
    cV
    @34
    cY
    cramerimp.v
    eleq2i
    biimpi
    adantl
    anim12i
    3adant3
    @2
    @5
    @6
    simp3
    #
    @33
    @36
    wa
    @6
    @30
    cX
    @15
    @22
    cV
    cR
    c.x
    @34
    cN
    cN
    ccrg
    cZ
    cY
    @16
    @22
    eqid
    cramerimp.v
    cramerimp.x
    @34
    eqid
    mavmulsolcl
    imp
    syl21anc
    #
    @2
    @5
    @1
    @6
    @0
    @1
    simpr
    3ad2ant1
    #
    @29
    @30
    @1
    wa
    wa
    cE
    cI
    cA
    cur
    cfv
    #
    cZ
    cN
    cR
    cmatrepV
    co
    #
    co
    cfv
    cB
    cramerimp.e
    cA
    cB
    cZ
    cR
    @40
    cI
    cN
    cV
    cramerimp.a
    cramerimp.b
    cramerimp.v
    @40
    eqid
    #
    ma1repvcl
    syl5eqel
    syl12anc
    @2
    @5
    @22
    cB
    wceq
    #
    @6
    @0
    @3
    @43
    @1
    @4
    @25
    cB
    @22
    @27
    eqcomd
    ad2ant2r
    3adant3
    eleqtrrd
    mamuval
    @7
    vi
    vj
    cN
    cN
    @12
    @13
    @7
    @8
    cN
    wcel
    #
    @10
    cN
    wcel
    #
    w3a
    @28
    @3
    @30
    @1
    w3a
    #
    @44
    @45
    @6
    @12
    @13
    wceq
    @7
    @44
    @28
    @45
    @2
    @5
    @28
    @6
    @31
    3ad2ant1
    3ad2ant1
    @7
    @44
    @46
    @45
    @7
    @3
    @30
    @1
    @5
    @2
    @3
    @6
    @3
    @4
    simpl
    3ad2ant2
    #
    @38
    @39
    3jca
    3ad2ant1
    @7
    @44
    @45
    simp2
    @7
    @44
    @45
    simp3
    @7
    @44
    @6
    @45
    @37
    3ad2ant1
    cA
    cB
    cZ
    cR
    c.x
    @40
    cE
    @8
    @10
    cI
    cN
    cV
    cX
    cR
    c0g
    cfv
    #
    cY
    vl
    cramerimp.a
    cramerimp.b
    cramerimp.v
    @42
    @48
    eqid
    cramerimp.e
    cramerimp.x
    mulmarep1gsum2
    syl113anc
    mpt2eq3dva
    @7
    cH
    cI
    cX
    cY
    @41
    co
    cfv
    #
    @14
    cramerimp.h
    @7
    @3
    @4
    @1
    @49
    @14
    wceq
    @47
    @5
    @2
    @4
    @6
    @3
    @4
    simpr
    3ad2ant2
    @39
    cA
    cB
    cY
    @41
    cR
    vi
    vj
    cI
    cX
    cN
    cV
    cramerimp.a
    cramerimp.b
    @41
    eqid
    cramerimp.v
    marepvval
    syl3anc
    syl5req
    3eqtrd
end
