include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "eqid.mm"
include "erngbase-rN.mm"
include "eqcomd.mm"
include "adantr.mm"
include "cmulr.mm"
include "ccom.mm"
include "cmpt2.mm"
include "erngfmul-rN.mm"
include "syl6reqr.mm"
include "c0g.mm"
include "cplusg.mm"
include "co.mm"
include "tendo0cl.mm"
include "eleqtrrd.mm"
include "cmpt.mm"
include "erngfplus-rN.mm"
include "oveqd.mm"
include "tendo0pl.mm"
include "mpdan.mm"
include "eqtr3d.mm"
include "cgrp.mm"
include "wb.mm"
include "erngdvlem1-rN.mm"
include "isgrpid2.mm"
include "syl.mm"
include "mpbi2and.mm"
include "cur.mm"
include "wral.mm"
include "tendoidcl.mm"
include "eleq2d.mm"
include "simpl.mm"
include "simpr.mm"
include "erngmul-rN.mm"
include "syl12anc.mm"
include "tendo1mulr.mm"
include "eqtrd.mm"
include "tendo1mul.mm"
include "jca.mm"
include "ex.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "crg.mm"
include "erngdvlem3-rN.mm"
include "isringid.mm"
include "w3a.mm"
include "simp1l.mm"
include "simp2l.mm"
include "simp3l.mm"
include "simp3.mm"
include "simp2.mm"
include "tendoconid.mm"
include "syl3anc.mm"
include "eqnetrd.mm"
include "tendo1ne0.mm"
include "simpll.mm"
include "simplrl.mm"
include "cdleml6.mm"
include "simpld.mm"
include "cdleml9.mm"
include "3expa.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "cdleml8.mm"
include "isdrngrd.mm"

theorem erngdvlem4-rN
  let vz: setvar z
  let cB: class B
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cE: class E
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let cM: class M
  let c.an: class ./\
  let cO: class O
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vt: setvar t
  let vu: setvar u
  assume ernggrp.h-r: |- H = ( LHyp ` K )
  assume ernggrp.d-r: |- D = ( ( EDRingR ` K ) ` W )
  assume ernggrplem.b-r: |- B = ( Base ` K )
  assume ernggrplem.t-r: |- T = ( ( LTrn ` K ) ` W )
  assume ernggrplem.e-r: |- E = ( ( TEndo ` K ) ` W )
  assume ernggrplem.p-r: |- P = ( a e. E , b e. E |-> ( f e. T |-> ( ( a ` f ) o. ( b ` f ) ) ) )
  assume ernggrplem.o-r: |- O = ( f e. T |-> ( _I |` B ) )
  assume ernggrplem.i-r: |- I = ( a e. E |-> ( f e. T |-> `' ( a ` f ) ) )
  assume erngrnglem.m-r: |- M = ( a e. E , b e. E |-> ( b o. a ) )
  assume edlemk6.j-r: |- .\/ = ( join ` K )
  assume edlemk6.m-r: |- ./\ = ( meet ` K )
  assume edlemk6.r-r: |- R = ( ( trL ` K ) ` W )
  assume edlemk6.p-r: |- Q = ( ( oc ` K ) ` W )
  assume edlemk6.z-r: |- Z = ( ( Q .\/ ( R ` b ) ) ./\ ( ( h ` Q ) .\/ ( R ` ( b o. `' ( s ` h ) ) ) ) )
  assume edlemk6.y-r: |- Y = ( ( Q .\/ ( R ` g ) ) ./\ ( Z .\/ ( R ` ( g o. `' b ) ) ) )
  assume edlemk6.x-r: |- X = ( iota_ z e. T A. b e. T ( ( b =/= ( _I |` B ) /\ ( R ` b ) =/= ( R ` ( s ` h ) ) /\ ( R ` b ) =/= ( R ` g ) ) -> ( z ` Q ) = Y ) )
  assume edlemk6.u-r: |- U = ( g e. T |-> if ( ( s ` h ) = h , g , X ) )

  disjoint b g
  disjoint b z
  disjoint ./\ b
  disjoint g z
  disjoint ./\ g
  disjoint ./\ z
  disjoint .\/ b
  disjoint .\/ g
  disjoint .\/ z
  disjoint b s
  disjoint B b
  disjoint g s
  disjoint B g
  disjoint s z
  disjoint B s
  disjoint B z
  disjoint H b
  disjoint H g
  disjoint H z
  disjoint K b
  disjoint K g
  disjoint K z
  disjoint M s
  disjoint P g
  disjoint P z
  disjoint Q b
  disjoint Q g
  disjoint Q z
  disjoint R b
  disjoint R g
  disjoint R z
  disjoint T b
  disjoint T g
  disjoint T z
  disjoint W b
  disjoint W g
  disjoint W z
  disjoint Y z
  disjoint Z g
  disjoint f g
  disjoint f z
  disjoint b h
  disjoint g h
  disjoint h s
  disjoint h z
  disjoint B f
  disjoint D s
  disjoint a b
  disjoint a s
  disjoint E a
  disjoint b s
  disjoint E b
  disjoint E s
  disjoint a f
  disjoint K a
  disjoint b f
  disjoint K b
  disjoint f s
  disjoint K f
  disjoint K s
  disjoint H f
  disjoint H s
  disjoint O s
  disjoint T a
  disjoint T b
  disjoint T f
  disjoint T s
  disjoint W a
  disjoint W b
  disjoint W f
  disjoint W s
  disjoint P s
  disjoint b t
  disjoint g t
  disjoint s t
  disjoint t z
  disjoint B t
  disjoint M t
  disjoint O t
  disjoint b u
  disjoint g u
  disjoint t u
  disjoint T t
  disjoint u z
  disjoint T u
  disjoint U t
  disjoint h t
  disjoint s t
  disjoint s u
  disjoint t u
  disjoint D t
  disjoint D u
  disjoint a t
  disjoint a u
  disjoint b t
  disjoint b u
  disjoint E t
  disjoint E u
  disjoint I t
  disjoint f t
  disjoint f u
  disjoint K t
  disjoint K u
  disjoint H t
  disjoint H u
  disjoint O t
  disjoint O u
  disjoint W t
  disjoint W u
  disjoint P t
  disjoint P u
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( h e. T /\ h =/= ( _I |` B ) ) ) -> D e. DivRing )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    vh
    cv
    #
    cT
    wcel
    #
    @1
    cid
    cB
    cres
    wne
    #
    wa
    #
    wa
    #
    vs
    vt
    cE
    cD
    cM
    cid
    cT
    cres
    #
    cU
    cO
    @0
    cE
    cD
    cbs
    cfv
    #
    wceq
    @4
    @0
    @7
    cE
    @7
    cD
    cT
    cE
    cH
    cK
    chlt
    cW
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrp.d-r
    @7
    eqid
    #
    erngbase-rN
    #
    eqcomd
    adantr
    @0
    cM
    cD
    cmulr
    cfv
    #
    wceq
    @4
    @0
    @10
    va
    vb
    cE
    cE
    vb
    cv
    #
    va
    cv
    #
    ccom
    cmpt2
    cM
    vb
    cD
    cT
    @10
    cE
    cH
    cK
    chlt
    cW
    va
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrp.d-r
    @10
    eqid
    #
    erngfmul-rN
    erngrnglem.m-r
    syl6reqr
    #
    adantr
    @0
    cO
    cD
    c0g
    cfv
    #
    wceq
    @4
    @0
    @15
    cO
    @0
    cO
    @7
    wcel
    #
    cO
    cO
    cD
    cplusg
    cfv
    #
    co
    #
    cO
    wceq
    #
    @15
    cO
    wceq
    #
    @0
    cO
    cE
    @7
    cB
    cT
    vf
    cE
    cH
    cK
    cO
    cW
    ernggrplem.b-r
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrplem.o-r
    tendo0cl
    #
    @9
    eleqtrrd
    @0
    cO
    cO
    cP
    co
    #
    @18
    cO
    @0
    cP
    @17
    cO
    cO
    @0
    @17
    va
    vb
    cE
    cE
    vf
    cT
    vf
    cv
    #
    @12
    cfv
    @23
    @11
    cfv
    ccom
    cmpt
    cmpt2
    cP
    vb
    cD
    @17
    cT
    vf
    cE
    cH
    cK
    chlt
    cW
    va
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrp.d-r
    @17
    eqid
    #
    erngfplus-rN
    ernggrplem.p-r
    syl6reqr
    oveqd
    @0
    cO
    cE
    wcel
    @22
    cO
    wceq
    @21
    vb
    cB
    cP
    cO
    cT
    vf
    cE
    cH
    cK
    cO
    cW
    va
    ernggrplem.b-r
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrplem.o-r
    ernggrplem.p-r
    tendo0pl
    mpdan
    eqtr3d
    @0
    cD
    cgrp
    wcel
    @16
    @19
    wa
    @20
    wb
    cB
    cD
    cP
    cT
    vf
    cE
    cH
    cI
    cK
    cO
    cW
    va
    vb
    ernggrp.h-r
    ernggrp.d-r
    ernggrplem.b-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrplem.p-r
    ernggrplem.o-r
    ernggrplem.i-r
    erngdvlem1-rN
    @7
    @17
    cD
    @15
    cO
    @8
    @24
    @15
    eqid
    isgrpid2
    syl
    mpbi2and
    eqcomd
    adantr
    @0
    @6
    cD
    cur
    cfv
    #
    wceq
    @4
    @0
    @25
    @6
    @0
    @6
    @7
    wcel
    #
    @6
    vu
    cv
    #
    @10
    co
    #
    @27
    wceq
    #
    @27
    @6
    @10
    co
    #
    @27
    wceq
    #
    wa
    #
    vu
    @7
    wral
    #
    @25
    @6
    wceq
    #
    @0
    @6
    cE
    @7
    cT
    cE
    cH
    cK
    cW
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    tendoidcl
    #
    @9
    eleqtrrd
    @0
    @32
    vu
    @7
    @0
    @27
    @7
    wcel
    @27
    cE
    wcel
    #
    @32
    @0
    @7
    cE
    @27
    @9
    eleq2d
    @0
    @36
    @32
    @0
    @36
    wa
    #
    @29
    @31
    @37
    @28
    @27
    @6
    ccom
    #
    @27
    @37
    @0
    @6
    cE
    wcel
    #
    @36
    @28
    @38
    wceq
    @0
    @36
    simpl
    #
    @0
    @39
    @36
    @35
    adantr
    #
    @0
    @36
    simpr
    #
    cD
    cT
    @10
    @6
    cE
    cH
    cK
    @27
    cW
    chlt
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrp.d-r
    @13
    erngmul-rN
    syl12anc
    cT
    @27
    cE
    cH
    cK
    cW
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    tendo1mulr
    eqtrd
    @37
    @30
    @6
    @27
    ccom
    #
    @27
    @37
    @0
    @36
    @39
    @30
    @43
    wceq
    @40
    @42
    @41
    cD
    cT
    @10
    @27
    cE
    cH
    cK
    @6
    cW
    chlt
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrp.d-r
    @13
    erngmul-rN
    syl12anc
    cT
    @27
    cE
    cH
    cK
    cW
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    tendo1mul
    eqtrd
    jca
    ex
    sylbid
    ralrimiv
    @0
    cD
    crg
    wcel
    #
    @26
    @33
    wa
    @34
    wb
    cB
    cD
    cP
    cT
    vf
    cE
    cH
    cI
    cK
    cM
    cO
    cW
    va
    vb
    ernggrp.h-r
    ernggrp.d-r
    ernggrplem.b-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrplem.p-r
    ernggrplem.o-r
    ernggrplem.i-r
    erngrnglem.m-r
    erngdvlem3-rN
    #
    vu
    @7
    cD
    @10
    @25
    @6
    @8
    @13
    @25
    eqid
    isringid
    syl
    mpbi2and
    eqcomd
    adantr
    @0
    @44
    @4
    @45
    adantr
    @5
    vs
    cv
    #
    cE
    wcel
    #
    @46
    cO
    wne
    #
    wa
    #
    vt
    cv
    #
    cE
    wcel
    #
    @50
    cO
    wne
    #
    wa
    #
    w3a
    #
    @46
    @50
    cM
    co
    #
    @50
    @46
    ccom
    #
    cO
    @54
    @55
    @46
    @50
    @10
    co
    #
    @56
    @54
    @0
    @55
    @57
    wceq
    @0
    @4
    @49
    @53
    simp1l
    #
    @0
    cM
    @10
    @46
    @50
    @14
    oveqd
    syl
    @54
    @0
    @47
    @51
    @57
    @56
    wceq
    @58
    @5
    @47
    @48
    @53
    simp2l
    @5
    @49
    @51
    @52
    simp3l
    cD
    cT
    @10
    @46
    cE
    cH
    cK
    @50
    cW
    chlt
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrp.d-r
    @13
    erngmul-rN
    syl12anc
    eqtrd
    @54
    @0
    @53
    @49
    @56
    cO
    wne
    @58
    @5
    @49
    @53
    simp3
    @5
    @49
    @53
    simp2
    cB
    cT
    @50
    vf
    cE
    cH
    cK
    cO
    @46
    cW
    ernggrplem.b-r
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrplem.o-r
    tendoconid
    syl3anc
    eqnetrd
    @0
    @6
    cO
    wne
    @4
    cB
    cT
    vf
    cE
    cH
    cK
    cO
    cW
    ernggrplem.b-r
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrplem.o-r
    tendo1ne0
    adantr
    @5
    @49
    wa
    #
    @0
    @2
    @49
    cU
    cE
    wcel
    #
    @0
    @4
    @49
    simpll
    #
    @0
    @2
    @3
    @49
    simplrl
    @5
    @49
    simpr
    @0
    @2
    @49
    w3a
    @60
    @1
    @46
    cfv
    cU
    cfv
    @1
    wceq
    vz
    cB
    cQ
    cR
    cT
    cU
    vf
    vg
    vh
    cE
    cH
    c.or
    cK
    c.an
    cW
    cX
    cY
    cO
    cZ
    vs
    vb
    ernggrplem.b-r
    edlemk6.j-r
    edlemk6.m-r
    ernggrp.h-r
    ernggrplem.t-r
    edlemk6.r-r
    edlemk6.p-r
    edlemk6.z-r
    edlemk6.y-r
    edlemk6.x-r
    edlemk6.u-r
    ernggrplem.e-r
    ernggrplem.o-r
    cdleml6
    simpld
    syl3anc
    #
    @0
    @4
    @49
    cU
    cO
    wne
    vz
    cB
    cQ
    cR
    cT
    cU
    vf
    vg
    vh
    cE
    cH
    c.or
    cK
    c.an
    cW
    cX
    cY
    cO
    cZ
    vs
    vb
    ernggrplem.b-r
    edlemk6.j-r
    edlemk6.m-r
    ernggrp.h-r
    ernggrplem.t-r
    edlemk6.r-r
    edlemk6.p-r
    edlemk6.z-r
    edlemk6.y-r
    edlemk6.x-r
    edlemk6.u-r
    ernggrplem.e-r
    ernggrplem.o-r
    cdleml9
    3expa
    @59
    @46
    cU
    cM
    co
    #
    @46
    cU
    @10
    co
    #
    @6
    @0
    @63
    @64
    wceq
    @4
    @49
    @0
    cM
    @10
    @46
    cU
    @14
    oveqd
    ad2antrr
    @59
    @64
    cU
    @46
    ccom
    #
    @6
    @59
    @0
    @47
    @60
    @64
    @65
    wceq
    @61
    @5
    @47
    @48
    simprl
    @62
    cD
    cT
    @10
    @46
    cE
    cH
    cK
    cU
    cW
    chlt
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrp.d-r
    @13
    erngmul-rN
    syl12anc
    @0
    @4
    @49
    @65
    @6
    wceq
    vz
    cB
    cQ
    cR
    cT
    cU
    vf
    vg
    vh
    cE
    cH
    c.or
    cK
    c.an
    cW
    cX
    cY
    cO
    cZ
    vs
    vb
    ernggrplem.b-r
    edlemk6.j-r
    edlemk6.m-r
    ernggrp.h-r
    ernggrplem.t-r
    edlemk6.r-r
    edlemk6.p-r
    edlemk6.z-r
    edlemk6.y-r
    edlemk6.x-r
    edlemk6.u-r
    ernggrplem.e-r
    ernggrplem.o-r
    cdleml8
    3expa
    eqtrd
    eqtrd
    isdrngrd
end
