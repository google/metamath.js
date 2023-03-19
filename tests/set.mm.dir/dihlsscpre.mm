include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "dihvalc.mm"
include "wreu.mm"
include "wrex.mm"
include "w3a.mm"
include "simp1l.mm"
include "simp2l.mm"
include "simp3ll.mm"
include "jca.mm"
include "simp2r.mm"
include "simp3rl.mm"
include "simp1rl.mm"
include "simp3lr.mm"
include "simp3rr.mm"
include "eqtr4d.mm"
include "dihjust.mm"
include "syl131anc.mm"
include "3exp.mm"
include "ralrimivv.mm"
include "wb.mm"
include "lhpmcvr2.mm"
include "clmod.mm"
include "simpll.mm"
include "dvhlmod.mm"
include "diclss.mm"
include "adantlr.mm"
include "clat.mm"
include "hllat.mm"
include "ad3antrrr.mm"
include "simplrl.mm"
include "lhpbase.mm"
include "ad3antlr.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "latmle2.mm"
include "diblss.mm"
include "syl12anc.mm"
include "lsmcl.mm"
include "a1d.mm"
include "expr.mm"
include "impd.mm"
include "ancld.mm"
include "reximdva.mm"
include "mpd.mm"
include "weq.mm"
include "breq1.mm"
include "notbid.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "reusv3.mm"
include "syl.mm"
include "mpbid.mm"
include "reusv1.mm"
include "mpbird.mm"
include "riotacl.mm"
include "eqeltrd.mm"

theorem dihlsscpre
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.po: class .(+)
  let cS: class S
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let vk: setvar k
  let vq: setvar q
  let vw: setvar w
  let vu: setvar u
  let vx: setvar x
  let vr: setvar r
  let cQ: class Q
  assume dihval.b: |- B = ( Base ` K )
  assume dihval.l: |- .<_ = ( le ` K )
  assume dihval.j: |- .\/ = ( join ` K )
  assume dihval.m: |- ./\ = ( meet ` K )
  assume dihval.a: |- A = ( Atoms ` K )
  assume dihval.h: |- H = ( LHyp ` K )
  assume dihval.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihval.d: |- D = ( ( DIsoB ` K ) ` W )
  assume dihval.c: |- C = ( ( DIsoC ` K ) ` W )
  assume dihval.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihval.s: |- S = ( LSubSp ` U )
  assume dihval.p: |- .(+) = ( LSSum ` U )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ -. X .<_ W ) ) -> ( I ` X ) e. S )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cX
    cB
    wcel
    #
    cX
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    wa
    #
    cX
    cI
    cfv
    vq
    cv
    #
    cW
    c.le
    wbr
    #
    wn
    #
    @7
    cX
    cW
    c.an
    co
    #
    c.or
    co
    #
    cX
    wceq
    #
    wa
    #
    vu
    cv
    @7
    cC
    cfv
    #
    @10
    cD
    cfv
    #
    c.po
    co
    #
    wceq
    wi
    vq
    cA
    wral
    #
    vu
    cS
    crio
    #
    cS
    vu
    cA
    cB
    cC
    cD
    c.po
    cS
    cU
    cH
    cI
    c.or
    cK
    c.le
    c.an
    chlt
    cW
    cX
    vq
    dihval.b
    dihval.l
    dihval.j
    dihval.m
    dihval.a
    dihval.h
    dihval.i
    dihval.d
    dihval.c
    dihval.u
    dihval.s
    dihval.p
    dihvalc
    @6
    @17
    vu
    cS
    wreu
    #
    @18
    cS
    wcel
    @6
    @19
    @17
    vu
    cS
    wrex
    #
    @6
    @13
    vr
    cv
    #
    cW
    c.le
    wbr
    #
    wn
    #
    @21
    @10
    c.or
    co
    #
    cX
    wceq
    #
    wa
    #
    wa
    #
    @16
    @21
    cC
    cfv
    #
    @15
    c.po
    co
    #
    wceq
    #
    wi
    #
    vr
    cA
    wral
    vq
    cA
    wral
    #
    @20
    @6
    @31
    vq
    vr
    cA
    cA
    @6
    @7
    cA
    wcel
    #
    @21
    cA
    wcel
    #
    wa
    #
    @27
    @30
    @6
    @35
    @27
    w3a
    #
    @2
    @33
    @9
    wa
    #
    @34
    @23
    wa
    @3
    @11
    @24
    wceq
    @30
    @2
    @5
    @35
    @27
    simp1l
    @36
    @33
    @9
    @6
    @33
    @34
    @27
    simp2l
    @9
    @12
    @26
    @6
    @35
    simp3ll
    jca
    @36
    @34
    @23
    @6
    @33
    @34
    @27
    simp2r
    @23
    @25
    @13
    @6
    @35
    simp3rl
    jca
    @3
    @4
    @2
    @35
    @27
    simp1rl
    @36
    @11
    cX
    @24
    @9
    @12
    @26
    @6
    @35
    simp3lr
    @23
    @25
    @13
    @6
    @35
    simp3rr
    eqtr4d
    cA
    cB
    c.po
    @7
    @21
    cU
    cH
    cD
    cC
    c.or
    cK
    c.le
    c.an
    cW
    cX
    dihval.b
    dihval.l
    dihval.j
    dihval.m
    dihval.a
    dihval.h
    dihval.d
    dihval.c
    dihval.u
    dihval.p
    dihjust
    syl131anc
    3exp
    ralrimivv
    @6
    @13
    @16
    cS
    wcel
    #
    wa
    #
    vq
    cA
    wrex
    #
    @32
    @20
    wb
    @6
    @13
    vq
    cA
    wrex
    #
    @40
    cA
    cB
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cX
    vq
    dihval.b
    dihval.l
    dihval.j
    dihval.m
    dihval.a
    dihval.h
    lhpmcvr2
    #
    @6
    @13
    @39
    vq
    cA
    @6
    @33
    wa
    #
    @13
    @38
    @43
    @9
    @12
    @38
    @6
    @33
    @9
    @12
    @38
    wi
    @6
    @37
    wa
    #
    @38
    @12
    @44
    cU
    clmod
    wcel
    @14
    cS
    wcel
    #
    @15
    cS
    wcel
    #
    @38
    @44
    cU
    cH
    cK
    cW
    dihval.h
    dihval.u
    @2
    @5
    @37
    simpll
    #
    dvhlmod
    @2
    @37
    @45
    @5
    cA
    @7
    cS
    cU
    cH
    cC
    cK
    c.le
    cW
    dihval.l
    dihval.a
    dihval.h
    dihval.u
    dihval.c
    dihval.s
    diclss
    adantlr
    @44
    @2
    @10
    cB
    wcel
    #
    @10
    cW
    c.le
    wbr
    #
    @46
    @47
    @44
    cK
    clat
    wcel
    #
    @3
    cW
    cB
    wcel
    #
    @48
    @0
    @50
    @1
    @5
    @37
    cK
    hllat
    ad3antrrr
    #
    @2
    @3
    @4
    @37
    simplrl
    #
    @1
    @51
    @0
    @5
    @37
    cB
    cH
    cK
    cW
    dihval.b
    dihval.h
    lhpbase
    ad3antlr
    #
    cB
    cK
    c.an
    cX
    cW
    dihval.b
    dihval.m
    latmcl
    syl3anc
    @44
    @50
    @3
    @51
    @49
    @52
    @53
    @54
    cB
    cK
    c.le
    c.an
    cX
    cW
    dihval.b
    dihval.l
    dihval.m
    latmle2
    syl3anc
    cB
    cS
    cU
    cH
    cD
    cK
    c.le
    cW
    @10
    dihval.b
    dihval.l
    dihval.h
    dihval.u
    dihval.d
    dihval.s
    diblss
    syl12anc
    c.po
    cS
    @14
    @15
    cU
    dihval.s
    dihval.p
    lsmcl
    syl3anc
    a1d
    expr
    impd
    ancld
    reximdva
    mpd
    @13
    @26
    vu
    vq
    vr
    cS
    cA
    @16
    @29
    vq
    vr
    weq
    #
    @9
    @23
    @12
    @25
    @55
    @8
    @22
    @7
    @21
    cW
    c.le
    breq1
    notbid
    @55
    @11
    @24
    cX
    @7
    @21
    @10
    c.or
    oveq1
    eqeq1d
    anbi12d
    @55
    @14
    @28
    @15
    c.po
    @7
    @21
    cC
    fveq2
    oveq1d
    reusv3
    syl
    mpbid
    @6
    @41
    @19
    @20
    wb
    @42
    @13
    vu
    vq
    cS
    cA
    @16
    reusv1
    syl
    mpbird
    @17
    vu
    cS
    riotacl
    syl
    eqeltrd
end
