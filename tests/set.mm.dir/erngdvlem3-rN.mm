include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "erngbase-rN.mm"
include "eqcomd.mm"
include "cplusg.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "erngfplus-rN.mm"
include "syl6reqr.mm"
include "cmulr.mm"
include "erngfmul-rN.mm"
include "erngdvlem1-rN.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "oveqd.mm"
include "3ad2ant1.mm"
include "erngmul-rN.mm"
include "3impb.mm"
include "eqtrd.mm"
include "tendococl.mm"
include "3com23.mm"
include "eqeltrd.mm"
include "oveqdr.mm"
include "3adantr1.mm"
include "coeq1d.mm"
include "adantr.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr3.mm"
include "simpr2.mm"
include "syl3anc.mm"
include "syl12anc.mm"
include "3adant3r3.mm"
include "3adantr3.mm"
include "coeq2d.mm"
include "3eqtrd.mm"
include "coass.mm"
include "syl6eqr.mm"
include "3eqtr4rd.mm"
include "tendodi2.mm"
include "syl13anc.mm"
include "tendoplcl.mm"
include "3adantr2.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "tendodi1.mm"
include "tendoidcl.mm"
include "simpr.mm"
include "tendo1mulr.mm"
include "tendo1mul.mm"
include "isringd.mm"

theorem erngdvlem3-rN
  let cB: class B
  let cD: class D
  let cP: class P
  let cT: class T
  let vf: setvar f
  let cE: class E
  let cH: class H
  let cI: class I
  let cK: class K
  let cM: class M
  let cO: class O
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vs: setvar s
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
  disjoint O s
  disjoint O t
  disjoint O u
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
    cM
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
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrp.d-r
    @2
    eqid
    erngbase-rN
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
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrp.d-r
    @3
    eqid
    erngfplus-rN
    ernggrplem.p-r
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
    @6
    @5
    ccom
    cmpt2
    cM
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
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrp.d-r
    @7
    eqid
    #
    erngfmul-rN
    erngrnglem.m-r
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
    cM
    co
    #
    @12
    @10
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
    cM
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
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrp.d-r
    @8
    erngmul-rN
    #
    3impb
    eqtrd
    @0
    @13
    @11
    @16
    cE
    wcel
    @12
    @10
    cE
    cH
    cK
    cW
    ernggrp.h-r
    ernggrplem.e-r
    tendococl
    3com23
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
    @12
    @21
    cM
    co
    #
    @10
    ccom
    #
    @21
    @12
    ccom
    #
    @10
    ccom
    #
    @10
    @25
    cM
    co
    #
    @15
    @21
    cM
    co
    #
    @24
    @25
    @27
    @10
    @24
    @25
    @12
    @21
    @7
    co
    #
    @27
    @0
    @23
    vt
    vu
    cM
    @7
    @9
    oveqdr
    @0
    @13
    @22
    @31
    @27
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
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrp.d-r
    @8
    erngmul-rN
    3adantr1
    eqtrd
    #
    coeq1d
    @24
    @29
    @10
    @25
    @7
    co
    #
    @26
    @0
    @29
    @33
    wceq
    @23
    @0
    cM
    @7
    @10
    @25
    @9
    oveqd
    adantr
    @24
    @0
    @11
    @25
    cE
    wcel
    @33
    @26
    wceq
    @0
    @23
    simpl
    #
    @0
    @11
    @13
    @22
    simpr1
    #
    @24
    @25
    @27
    cE
    @32
    @24
    @0
    @22
    @13
    @27
    cE
    wcel
    @34
    @0
    @11
    @13
    @22
    simpr3
    #
    @0
    @11
    @13
    @22
    simpr2
    #
    @21
    @12
    cE
    cH
    cK
    cW
    ernggrp.h-r
    ernggrplem.e-r
    tendococl
    syl3anc
    eqeltrd
    cD
    cT
    @7
    @10
    cE
    cH
    cK
    @25
    cW
    chlt
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrp.d-r
    @8
    erngmul-rN
    syl12anc
    eqtrd
    @24
    @30
    @21
    @16
    ccom
    #
    @28
    @24
    @30
    @15
    @21
    @7
    co
    #
    @21
    @15
    ccom
    #
    @38
    @0
    @30
    @39
    wceq
    @23
    @0
    cM
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
    @39
    @40
    wceq
    @34
    @0
    @11
    @13
    @41
    @22
    @20
    3adant3r3
    @36
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
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrp.d-r
    @8
    erngmul-rN
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
    cM
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
    coeq2d
    3eqtrd
    @21
    @12
    @10
    coass
    syl6eqr
    3eqtr4rd
    @24
    @12
    @21
    cP
    co
    #
    @10
    ccom
    #
    @16
    @21
    @10
    ccom
    #
    cP
    co
    #
    @10
    @43
    cM
    co
    #
    @15
    @10
    @21
    cM
    co
    #
    cP
    co
    @24
    @0
    @13
    @22
    @11
    @44
    @46
    wceq
    @34
    @37
    @36
    @35
    vb
    cP
    @12
    cT
    @21
    vf
    cE
    cH
    cK
    @10
    cW
    va
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrplem.p-r
    tendodi2
    syl13anc
    @24
    @47
    @10
    @43
    @7
    co
    #
    @44
    @0
    @47
    @49
    wceq
    @23
    @0
    cM
    @7
    @10
    @43
    @9
    oveqd
    adantr
    @24
    @0
    @11
    @43
    cE
    wcel
    #
    @49
    @44
    wceq
    @34
    @35
    @24
    @0
    @13
    @22
    @50
    @34
    @37
    @36
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
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrplem.p-r
    tendoplcl
    syl3anc
    cD
    cT
    @7
    @10
    cE
    cH
    cK
    @43
    cW
    chlt
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrp.d-r
    @8
    erngmul-rN
    syl12anc
    eqtrd
    @24
    @15
    @16
    @48
    @45
    cP
    @42
    @24
    @48
    @10
    @21
    @7
    co
    #
    @45
    @0
    @23
    vs
    vu
    cM
    @7
    @9
    oveqdr
    @0
    @11
    @22
    @51
    @45
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
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrp.d-r
    @8
    erngmul-rN
    3adantr2
    eqtrd
    #
    oveq12d
    3eqtr4d
    @24
    @21
    @10
    @12
    cP
    co
    #
    ccom
    #
    @45
    @27
    cP
    co
    #
    @53
    @21
    cM
    co
    #
    @48
    @25
    cP
    co
    @24
    @0
    @22
    @11
    @13
    @54
    @55
    wceq
    @34
    @36
    @35
    @37
    vb
    cP
    @21
    cT
    @10
    vf
    cE
    cH
    cK
    @12
    cW
    va
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrplem.p-r
    tendodi1
    syl13anc
    @24
    @56
    @53
    @21
    @7
    co
    #
    @54
    @24
    cM
    @7
    @53
    @21
    @0
    cM
    @7
    wceq
    @23
    @9
    adantr
    oveqd
    @24
    @0
    @53
    cE
    wcel
    #
    @22
    @57
    @54
    wceq
    @34
    @0
    @11
    @13
    @58
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
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrplem.p-r
    tendoplcl
    3adant3r3
    @36
    cD
    cT
    @7
    @53
    cE
    cH
    cK
    @21
    cW
    chlt
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrp.d-r
    @8
    erngmul-rN
    syl12anc
    eqtrd
    @24
    @48
    @45
    @25
    @27
    cP
    @52
    @32
    oveq12d
    3eqtr4d
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
    @0
    @11
    wa
    #
    @1
    @10
    cM
    co
    #
    @1
    @10
    @7
    co
    #
    @10
    @1
    ccom
    #
    @10
    @0
    @61
    @62
    wceq
    @11
    @0
    cM
    @7
    @1
    @10
    @9
    oveqd
    adantr
    @60
    @0
    @1
    cE
    wcel
    #
    @11
    @62
    @63
    wceq
    @0
    @11
    simpl
    #
    @0
    @64
    @11
    @59
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
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrp.d-r
    @8
    erngmul-rN
    syl12anc
    cT
    @10
    cE
    cH
    cK
    cW
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    tendo1mulr
    3eqtrd
    @60
    @10
    @1
    cM
    co
    #
    @10
    @1
    @7
    co
    #
    @1
    @10
    ccom
    #
    @10
    @0
    @68
    @69
    wceq
    @11
    @0
    cM
    @7
    @10
    @1
    @9
    oveqd
    adantr
    @60
    @0
    @11
    @64
    @69
    @70
    wceq
    @65
    @67
    @66
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
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrp.d-r
    @8
    erngmul-rN
    syl12anc
    cT
    @10
    cE
    cH
    cK
    cW
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    tendo1mul
    3eqtrd
    isringd
end
