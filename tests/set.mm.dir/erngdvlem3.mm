include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "erngbase.mm"
include "eqcomd.mm"
include "cplusg.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "erngfplus.mm"
include "syl6reqr.mm"
include "cmulr.mm"
include "erngfmul.mm"
include "erngdvlem1.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "oveqd.mm"
include "3ad2ant1.mm"
include "erngmul.mm"
include "3impb.mm"
include "eqtrd.mm"
include "tendococl.mm"
include "eqeltrd.mm"
include "coass.mm"
include "adantr.mm"
include "simpl.mm"
include "3adant3r3.mm"
include "simpr3.mm"
include "syl12anc.mm"
include "oveqdr.mm"
include "3adantr3.mm"
include "coeq1d.mm"
include "3eqtrd.mm"
include "simpr1.mm"
include "3adantr1.mm"
include "3adant3r1.mm"
include "coeq2d.mm"
include "3eqtr4a.mm"
include "tendodi1.mm"
include "tendoplcl.mm"
include "3adantr2.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "tendodi2.mm"
include "tendoidcl.mm"
include "simpr.mm"
include "tendo1mul.mm"
include "tendo1mulr.mm"
include "isringd.mm"

theorem erngdvlem3
  let cB: class B
  let cD: class D
  let cP: class P
  let c.pl: class .+
  let cT: class T
  let vf: setvar f
  let cE: class E
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vs: setvar s
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

  disjoint B f
  disjoint a b
  disjoint E a
  disjoint E b
  disjoint a f
  disjoint K a
  disjoint b f
  disjoint K b
  disjoint K f
  disjoint H f
  disjoint T a
  disjoint T b
  disjoint T f
  disjoint W a
  disjoint W b
  disjoint W f
  disjoint s t
  disjoint s u
  disjoint D s
  disjoint t u
  disjoint D t
  disjoint D u
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint E s
  disjoint E t
  disjoint E u
  disjoint I t
  disjoint f s
  disjoint f t
  disjoint f u
  disjoint K s
  disjoint K t
  disjoint K u
  disjoint H s
  disjoint H t
  disjoint H u
  disjoint .0. s
  disjoint .0. t
  disjoint .0. u
  disjoint T s
  disjoint W s
  disjoint W t
  disjoint W u
  disjoint P s
  disjoint P t
  disjoint P u
  assert |- ( ( K e. HL /\ W e. H ) -> D e. Ring )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    vs
    vt
    vu
    cE
    cP
    cD
    c.pl
    cid
    cT
    cres
    #
    @0
    cD
    cbs
    cfv
    #
    cE
    @2
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
    @2
    eqid
    erngbase
    eqcomd
    @0
    cD
    cplusg
    cfv
    #
    va
    vb
    cE
    cE
    vf
    cT
    vf
    cv
    #
    va
    cv
    #
    cfv
    @4
    vb
    cv
    #
    cfv
    ccom
    cmpt
    cmpt2
    cP
    vb
    cD
    @3
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
    @3
    eqid
    erngfplus
    erngdv.p
    syl6reqr
    @0
    cD
    cmulr
    cfv
    #
    va
    vb
    cE
    cE
    @5
    @6
    ccom
    cmpt2
    c.pl
    vb
    cD
    cT
    @7
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
    @7
    eqid
    #
    erngfmul
    erngrnglem.m
    syl6reqr
    #
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
    @0
    vs
    cv
    #
    cE
    wcel
    #
    vt
    cv
    #
    cE
    wcel
    #
    w3a
    #
    @10
    @12
    c.pl
    co
    #
    @10
    @12
    ccom
    #
    cE
    @14
    @15
    @10
    @12
    @7
    co
    #
    @16
    @0
    @11
    @15
    @17
    wceq
    @13
    @0
    c.pl
    @7
    @10
    @12
    @9
    oveqd
    3ad2ant1
    @0
    @11
    @13
    @17
    @16
    wceq
    #
    cD
    cT
    @7
    @10
    cE
    cH
    cK
    @12
    cW
    chlt
    ernggrp.h
    erngdv.t
    erngdv.e
    ernggrp.d
    @8
    erngmul
    #
    3impb
    eqtrd
    @10
    @12
    cE
    cH
    cK
    cW
    ernggrp.h
    erngdv.e
    tendococl
    eqeltrd
    #
    @0
    @11
    @13
    vu
    cv
    #
    cE
    wcel
    #
    w3a
    #
    wa
    #
    @16
    @21
    ccom
    #
    @10
    @12
    @21
    ccom
    #
    ccom
    #
    @15
    @21
    c.pl
    co
    #
    @10
    @12
    @21
    c.pl
    co
    #
    c.pl
    co
    #
    @10
    @12
    @21
    coass
    @24
    @28
    @15
    @21
    @7
    co
    #
    @15
    @21
    ccom
    #
    @25
    @0
    @28
    @31
    wceq
    @23
    @0
    c.pl
    @7
    @15
    @21
    @9
    oveqd
    adantr
    @24
    @0
    @15
    cE
    wcel
    #
    @22
    @31
    @32
    wceq
    @0
    @23
    simpl
    #
    @0
    @11
    @13
    @33
    @22
    @20
    3adant3r3
    @0
    @11
    @13
    @22
    simpr3
    #
    cD
    cT
    @7
    @15
    cE
    cH
    cK
    @21
    cW
    chlt
    ernggrp.h
    erngdv.t
    erngdv.e
    ernggrp.d
    @8
    erngmul
    syl12anc
    @24
    @15
    @16
    @21
    @24
    @15
    @17
    @16
    @0
    @23
    vs
    vt
    c.pl
    @7
    @9
    oveqdr
    @0
    @11
    @13
    @18
    @22
    @19
    3adantr3
    eqtrd
    #
    coeq1d
    3eqtrd
    @24
    @30
    @10
    @29
    @7
    co
    #
    @10
    @29
    ccom
    #
    @27
    @0
    @30
    @37
    wceq
    @23
    @0
    c.pl
    @7
    @10
    @29
    @9
    oveqd
    adantr
    @24
    @0
    @11
    @29
    cE
    wcel
    @37
    @38
    wceq
    @34
    @0
    @11
    @13
    @22
    simpr1
    #
    @24
    @29
    @26
    cE
    @24
    @29
    @12
    @21
    @7
    co
    #
    @26
    @0
    @23
    vt
    vu
    c.pl
    @7
    @9
    oveqdr
    @0
    @13
    @22
    @40
    @26
    wceq
    @11
    cD
    cT
    @7
    @12
    cE
    cH
    cK
    @21
    cW
    chlt
    ernggrp.h
    erngdv.t
    erngdv.e
    ernggrp.d
    @8
    erngmul
    3adantr1
    eqtrd
    #
    @0
    @13
    @22
    @26
    cE
    wcel
    @11
    @12
    @21
    cE
    cH
    cK
    cW
    ernggrp.h
    erngdv.e
    tendococl
    3adant3r1
    eqeltrd
    cD
    cT
    @7
    @10
    cE
    cH
    cK
    @29
    cW
    chlt
    ernggrp.h
    erngdv.t
    erngdv.e
    ernggrp.d
    @8
    erngmul
    syl12anc
    @24
    @29
    @26
    @10
    @41
    coeq2d
    3eqtrd
    3eqtr4a
    @24
    @10
    @12
    @21
    cP
    co
    #
    ccom
    #
    @16
    @10
    @21
    ccom
    #
    cP
    co
    @10
    @42
    c.pl
    co
    #
    @15
    @10
    @21
    c.pl
    co
    #
    cP
    co
    vb
    cP
    @10
    cT
    @12
    vf
    cE
    cH
    cK
    @21
    cW
    va
    ernggrp.h
    erngdv.t
    erngdv.e
    erngdv.p
    tendodi1
    @24
    @45
    @10
    @42
    @7
    co
    #
    @43
    @0
    @45
    @47
    wceq
    @23
    @0
    c.pl
    @7
    @10
    @42
    @9
    oveqd
    adantr
    @24
    @0
    @11
    @42
    cE
    wcel
    #
    @47
    @43
    wceq
    @34
    @39
    @0
    @13
    @22
    @48
    @11
    vb
    cP
    cT
    @12
    vf
    cE
    cH
    cK
    @21
    cW
    va
    ernggrp.h
    erngdv.t
    erngdv.e
    erngdv.p
    tendoplcl
    3adant3r1
    cD
    cT
    @7
    @10
    cE
    cH
    cK
    @42
    cW
    chlt
    ernggrp.h
    erngdv.t
    erngdv.e
    ernggrp.d
    @8
    erngmul
    syl12anc
    eqtrd
    @24
    @15
    @16
    @46
    @44
    cP
    @36
    @24
    @46
    @10
    @21
    @7
    co
    #
    @44
    @0
    @23
    vs
    vu
    c.pl
    @7
    @9
    oveqdr
    @0
    @11
    @22
    @49
    @44
    wceq
    @13
    cD
    cT
    @7
    @10
    cE
    cH
    cK
    @21
    cW
    chlt
    ernggrp.h
    erngdv.t
    erngdv.e
    ernggrp.d
    @8
    erngmul
    3adantr2
    eqtrd
    #
    oveq12d
    3eqtr4d
    @24
    @10
    @12
    cP
    co
    #
    @21
    ccom
    #
    @44
    @26
    cP
    co
    @51
    @21
    c.pl
    co
    #
    @46
    @29
    cP
    co
    vb
    cP
    @10
    cT
    @12
    vf
    cE
    cH
    cK
    @21
    cW
    va
    ernggrp.h
    erngdv.t
    erngdv.e
    erngdv.p
    tendodi2
    @24
    @53
    @51
    @21
    @7
    co
    #
    @52
    @0
    @53
    @54
    wceq
    @23
    @0
    c.pl
    @7
    @51
    @21
    @9
    oveqd
    adantr
    @24
    @0
    @51
    cE
    wcel
    #
    @22
    @54
    @52
    wceq
    @34
    @0
    @11
    @13
    @55
    @22
    vb
    cP
    cT
    @10
    vf
    cE
    cH
    cK
    @12
    cW
    va
    ernggrp.h
    erngdv.t
    erngdv.e
    erngdv.p
    tendoplcl
    3adant3r3
    @35
    cD
    cT
    @7
    @51
    cE
    cH
    cK
    @21
    cW
    chlt
    ernggrp.h
    erngdv.t
    erngdv.e
    ernggrp.d
    @8
    erngmul
    syl12anc
    eqtrd
    @24
    @46
    @44
    @29
    @26
    cP
    @50
    @41
    oveq12d
    3eqtr4d
    cT
    cE
    cH
    cK
    cW
    ernggrp.h
    erngdv.t
    erngdv.e
    tendoidcl
    #
    @0
    @11
    wa
    #
    @1
    @10
    c.pl
    co
    #
    @1
    @10
    @7
    co
    #
    @1
    @10
    ccom
    #
    @10
    @0
    @58
    @59
    wceq
    @11
    @0
    c.pl
    @7
    @1
    @10
    @9
    oveqd
    adantr
    @57
    @0
    @1
    cE
    wcel
    #
    @11
    @59
    @60
    wceq
    @0
    @11
    simpl
    #
    @0
    @61
    @11
    @56
    adantr
    #
    @0
    @11
    simpr
    #
    cD
    cT
    @7
    @1
    cE
    cH
    cK
    @10
    cW
    chlt
    ernggrp.h
    erngdv.t
    erngdv.e
    ernggrp.d
    @8
    erngmul
    syl12anc
    cT
    @10
    cE
    cH
    cK
    cW
    ernggrp.h
    erngdv.t
    erngdv.e
    tendo1mul
    3eqtrd
    @57
    @10
    @1
    c.pl
    co
    #
    @10
    @1
    @7
    co
    #
    @10
    @1
    ccom
    #
    @10
    @0
    @65
    @66
    wceq
    @11
    @0
    c.pl
    @7
    @10
    @1
    @9
    oveqd
    adantr
    @57
    @0
    @11
    @61
    @66
    @67
    wceq
    @62
    @64
    @63
    cD
    cT
    @7
    @10
    cE
    cH
    cK
    @1
    cW
    chlt
    ernggrp.h
    erngdv.t
    erngdv.e
    ernggrp.d
    @8
    erngmul
    syl12anc
    cT
    @10
    cE
    cH
    cK
    cW
    ernggrp.h
    erngdv.t
    erngdv.e
    tendo1mulr
    3eqtrd
    isringd
end
