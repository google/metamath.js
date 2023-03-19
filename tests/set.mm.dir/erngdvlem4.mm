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
include "erngbase.mm"
include "eqcomd.mm"
include "adantr.mm"
include "cmulr.mm"
include "ccom.mm"
include "cmpt2.mm"
include "erngfmul.mm"
include "syl6reqr.mm"
include "c0g.mm"
include "cplusg.mm"
include "co.mm"
include "tendo0cl.mm"
include "eleqtrrd.mm"
include "cmpt.mm"
include "erngfplus.mm"
include "oveqd.mm"
include "tendo0pl.mm"
include "mpdan.mm"
include "eqtr3d.mm"
include "cgrp.mm"
include "wb.mm"
include "erngdvlem1.mm"
include "isgrpid2.mm"
include "syl.mm"
include "mpbi2and.mm"
include "cur.mm"
include "erngdvlem3.mm"
include "erng1lem.mm"
include "crg.mm"
include "w3a.mm"
include "simp1l.mm"
include "simp2l.mm"
include "simp3l.mm"
include "erngmul.mm"
include "syl12anc.mm"
include "eqtrd.mm"
include "tendoconid.mm"
include "3adant1r.mm"
include "eqnetrd.mm"
include "tendo1ne0.mm"
include "simpll.mm"
include "simplrl.mm"
include "simpr.mm"
include "cdleml6.mm"
include "simpld.mm"
include "syl3anc.mm"
include "cdleml9.mm"
include "3expa.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "cdleml8.mm"
include "3eqtrd.mm"
include "isdrngd.mm"

theorem erngdvlem4
  let vz: setvar z
  let cB: class B
  let cD: class D
  let cP: class P
  let c.pl: class .+
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
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vt: setvar t
  let vu: setvar u
  assume ernggrp.h: |- H = ( LHyp ` K )
  assume ernggrp.d: |- D = ( ( EDRing ` K ) ` W )
  assume erngdv.b: |- B = ( Base ` K )
  assume erngdv.t: |- T = ( ( LTrn ` K ) ` W )
  assume erngdv.e: |- E = ( ( TEndo ` K ) ` W )
  assume erngdv.p: |- P = ( a e. E , b e. E |-> ( f e. T |-> ( ( a ` f ) o. ( b ` f ) ) ) )
  assume erngdv.o: |- .0. = ( f e. T |-> ( _I |` B ) )
  assume erngdv.i: |- I = ( a e. E |-> ( f e. T |-> `' ( a ` f ) ) )
  assume erngrnglem.m: |- .+ = ( a e. E , b e. E |-> ( a o. b ) )
  assume edlemk6.j: |- .\/ = ( join ` K )
  assume edlemk6.m: |- ./\ = ( meet ` K )
  assume edlemk6.r: |- R = ( ( trL ` K ) ` W )
  assume edlemk6.p: |- Q = ( ( oc ` K ) ` W )
  assume edlemk6.z: |- Z = ( ( Q .\/ ( R ` b ) ) ./\ ( ( h ` Q ) .\/ ( R ` ( b o. `' ( s ` h ) ) ) ) )
  assume edlemk6.y: |- Y = ( ( Q .\/ ( R ` g ) ) ./\ ( Z .\/ ( R ` ( g o. `' b ) ) ) )
  assume edlemk6.x: |- X = ( iota_ z e. T A. b e. T ( ( b =/= ( _I |` B ) /\ ( R ` b ) =/= ( R ` ( s ` h ) ) /\ ( R ` b ) =/= ( R ` g ) ) -> ( z ` Q ) = Y ) )
  assume edlemk6.u: |- U = ( g e. T |-> if ( ( s ` h ) = h , g , X ) )

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
  disjoint .+ s
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
  disjoint .0. s
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
  disjoint .+ t
  disjoint T t
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
  disjoint .0. t
  disjoint .0. u
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
    c.pl
    cid
    cT
    cres
    #
    cU
    c.0
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
    ernggrp.h
    erngdv.t
    erngdv.e
    ernggrp.d
    @7
    eqid
    #
    erngbase
    #
    eqcomd
    adantr
    @0
    c.pl
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
    va
    cv
    #
    vb
    cv
    #
    ccom
    cmpt2
    c.pl
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
    ernggrp.h
    erngdv.t
    erngdv.e
    ernggrp.d
    @10
    eqid
    #
    erngfmul
    erngrnglem.m
    syl6reqr
    #
    adantr
    @0
    c.0
    cD
    c0g
    cfv
    #
    wceq
    @4
    @0
    @15
    c.0
    @0
    c.0
    @7
    wcel
    #
    c.0
    c.0
    cD
    cplusg
    cfv
    #
    co
    #
    c.0
    wceq
    #
    @15
    c.0
    wceq
    #
    @0
    c.0
    cE
    @7
    cB
    cT
    vf
    cE
    cH
    cK
    c.0
    cW
    erngdv.b
    ernggrp.h
    erngdv.t
    erngdv.e
    erngdv.o
    tendo0cl
    #
    @9
    eleqtrrd
    @0
    c.0
    c.0
    cP
    co
    #
    @18
    c.0
    @0
    cP
    @17
    c.0
    c.0
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
    @11
    cfv
    @23
    @12
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
    ernggrp.h
    erngdv.t
    erngdv.e
    ernggrp.d
    @17
    eqid
    #
    erngfplus
    erngdv.p
    syl6reqr
    oveqd
    @0
    c.0
    cE
    wcel
    @22
    c.0
    wceq
    @21
    vb
    cB
    cP
    c.0
    cT
    vf
    cE
    cH
    cK
    c.0
    cW
    va
    erngdv.b
    ernggrp.h
    erngdv.t
    erngdv.e
    erngdv.o
    erngdv.p
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
    cW
    c.0
    va
    vb
    ernggrp.h
    ernggrp.d
    erngdv.b
    erngdv.t
    erngdv.e
    erngdv.p
    erngdv.o
    erngdv.i
    erngdvlem1
    @7
    @17
    cD
    @15
    c.0
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
    cD
    cT
    cE
    cH
    cK
    cW
    ernggrp.h
    erngdv.t
    erngdv.e
    ernggrp.d
    cB
    cD
    cP
    c.pl
    cT
    vf
    cE
    cH
    cI
    cK
    cW
    c.0
    va
    vb
    ernggrp.h
    ernggrp.d
    erngdv.b
    erngdv.t
    erngdv.e
    erngdv.p
    erngdv.o
    erngdv.i
    erngrnglem.m
    erngdvlem3
    #
    erng1lem
    eqcomd
    adantr
    @0
    cD
    crg
    wcel
    @4
    @26
    adantr
    @5
    vs
    cv
    #
    cE
    wcel
    #
    @27
    c.0
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
    @31
    c.0
    wne
    #
    wa
    #
    w3a
    #
    @27
    @31
    c.pl
    co
    #
    @27
    @31
    ccom
    #
    c.0
    @35
    @36
    @27
    @31
    @10
    co
    #
    @37
    @35
    @0
    @36
    @38
    wceq
    @0
    @4
    @30
    @34
    simp1l
    #
    @0
    c.pl
    @10
    @27
    @31
    @14
    oveqd
    syl
    @35
    @0
    @28
    @32
    @38
    @37
    wceq
    @39
    @5
    @28
    @29
    @34
    simp2l
    @5
    @30
    @32
    @33
    simp3l
    cD
    cT
    @10
    @27
    cE
    cH
    cK
    @31
    cW
    chlt
    ernggrp.h
    erngdv.t
    erngdv.e
    ernggrp.d
    @13
    erngmul
    syl12anc
    eqtrd
    @0
    @30
    @34
    @37
    c.0
    wne
    @4
    cB
    cT
    @27
    vf
    cE
    cH
    cK
    c.0
    @31
    cW
    erngdv.b
    ernggrp.h
    erngdv.t
    erngdv.e
    erngdv.o
    tendoconid
    3adant1r
    eqnetrd
    @0
    @6
    c.0
    wne
    @4
    cB
    cT
    vf
    cE
    cH
    cK
    c.0
    cW
    erngdv.b
    ernggrp.h
    erngdv.t
    erngdv.e
    erngdv.o
    tendo1ne0
    adantr
    @5
    @30
    wa
    #
    @0
    @2
    @30
    cU
    cE
    wcel
    #
    @0
    @4
    @30
    simpll
    #
    @0
    @2
    @3
    @30
    simplrl
    @5
    @30
    simpr
    @0
    @2
    @30
    w3a
    @41
    @1
    @27
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
    c.0
    cZ
    vs
    vb
    erngdv.b
    edlemk6.j
    edlemk6.m
    ernggrp.h
    erngdv.t
    edlemk6.r
    edlemk6.p
    edlemk6.z
    edlemk6.y
    edlemk6.x
    edlemk6.u
    erngdv.e
    erngdv.o
    cdleml6
    simpld
    syl3anc
    #
    @0
    @4
    @30
    cU
    c.0
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
    c.0
    cZ
    vs
    vb
    erngdv.b
    edlemk6.j
    edlemk6.m
    ernggrp.h
    erngdv.t
    edlemk6.r
    edlemk6.p
    edlemk6.z
    edlemk6.y
    edlemk6.x
    edlemk6.u
    erngdv.e
    erngdv.o
    cdleml9
    3expa
    @40
    cU
    @27
    c.pl
    co
    #
    cU
    @27
    @10
    co
    #
    cU
    @27
    ccom
    #
    @6
    @0
    @44
    @45
    wceq
    @4
    @30
    @0
    c.pl
    @10
    cU
    @27
    @14
    oveqd
    ad2antrr
    @40
    @0
    @41
    @28
    @45
    @46
    wceq
    @42
    @43
    @5
    @28
    @29
    simprl
    cD
    cT
    @10
    cU
    cE
    cH
    cK
    @27
    cW
    chlt
    ernggrp.h
    erngdv.t
    erngdv.e
    ernggrp.d
    @13
    erngmul
    syl12anc
    @0
    @4
    @30
    @46
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
    c.0
    cZ
    vs
    vb
    erngdv.b
    edlemk6.j
    edlemk6.m
    ernggrp.h
    erngdv.t
    edlemk6.r
    edlemk6.p
    edlemk6.z
    edlemk6.y
    edlemk6.x
    edlemk6.u
    erngdv.e
    erngdv.o
    cdleml8
    3expa
    3eqtrd
    isdrngd
end
