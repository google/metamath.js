include "ccrg.mm"
include "wcel.mm"
include "wa.mm"
include "crg.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "c2idl.mm"
include "crngring.mm"
include "adantr.mm"
include "simpr.mm"
include "crng2idl.mm"
include "eleqtrd.mm"
include "eqid.mm"
include "qusring.mm"
include "syl2anc.mm"
include "cqg.mm"
include "cqs.mm"
include "cvv.mm"
include "cqus.mm"
include "a1i.mm"
include "eqidd.mm"
include "ovexd.mm"
include "qusbas.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "cec.mm"
include "oveq2.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "crngcom.mm"
include "3adant1r.mm"
include "3expa.mm"
include "eceq1d.mm"
include "csubg.mm"
include "wer.mm"
include "lidlsubg.mm"
include "sylan.mm"
include "eqger.mm"
include "syl.mm"
include "wbr.mm"
include "wi.mm"
include "2idlcpbl.mm"
include "ringcl.mm"
include "3expb.mm"
include "qusmulval.mm"
include "an32s.mm"
include "3eqtr4rd.mm"
include "ectocld.mm"
include "expl.mm"
include "sylbird.mm"
include "ralrimivv.mm"
include "iscrng2.mm"
include "sylanbrc.mm"

theorem quscrng
  let cR: class R
  let cS: class S
  let cU: class U
  let cI: class I
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  assume quscrng.u: |- U = ( R /s ( R ~QG S ) )
  assume quscrng.i: |- I = ( LIdeal ` R )


  assert |- ( ( R e. CRing /\ S e. I ) -> U e. CRing )

  proof
    cR
    ccrg
    wcel
    #
    cS
    cI
    wcel
    #
    wa
    #
    cU
    crg
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cU
    cmulr
    cfv
    #
    co
    #
    @5
    @4
    @6
    co
    #
    wceq
    #
    vy
    cU
    cbs
    cfv
    #
    wral
    vx
    @10
    wral
    cU
    ccrg
    wcel
    @2
    cR
    crg
    wcel
    #
    cS
    cR
    c2idl
    cfv
    #
    wcel
    #
    @3
    @0
    @11
    @1
    cR
    crngring
    #
    adantr
    #
    @2
    cS
    cI
    @12
    @0
    @1
    simpr
    @0
    cI
    @12
    wceq
    @1
    cR
    cI
    quscrng.i
    crng2idl
    adantr
    eleqtrd
    #
    cR
    cS
    cU
    @12
    quscrng.u
    @12
    eqid
    #
    qusring
    syl2anc
    @2
    @9
    vx
    vy
    @10
    @10
    @2
    @4
    @10
    wcel
    #
    @5
    @10
    wcel
    #
    wa
    @4
    cR
    cbs
    cfv
    #
    cR
    cS
    cqg
    co
    #
    cqs
    #
    wcel
    #
    @5
    @22
    wcel
    #
    wa
    @9
    @2
    @23
    @18
    @24
    @19
    @2
    @22
    @10
    @4
    @2
    @21
    cR
    cU
    @20
    cvv
    crg
    cU
    cR
    @21
    cqus
    co
    wceq
    @2
    quscrng.u
    a1i
    #
    @2
    @20
    eqidd
    #
    @2
    cR
    cS
    cqg
    ovexd
    @15
    qusbas
    #
    eleq2d
    @2
    @22
    @10
    @5
    @27
    eleq2d
    anbi12d
    @2
    @23
    @24
    @9
    @4
    vu
    cv
    #
    @21
    cec
    #
    @6
    co
    #
    @29
    @4
    @6
    co
    #
    wceq
    #
    @9
    @2
    @23
    wa
    vu
    @5
    @20
    @21
    @22
    @22
    eqid
    #
    @29
    @5
    wceq
    @30
    @7
    @31
    @8
    @29
    @5
    @4
    @6
    oveq2
    @29
    @5
    @4
    @6
    oveq1
    eqeq12d
    @2
    @28
    @20
    wcel
    #
    @23
    @32
    vv
    cv
    #
    @21
    cec
    #
    @29
    @6
    co
    #
    @29
    @36
    @6
    co
    #
    wceq
    @32
    @2
    @34
    wa
    #
    vv
    @4
    @20
    @21
    @22
    @33
    @36
    @4
    wceq
    @37
    @30
    @38
    @31
    @36
    @4
    @29
    @6
    oveq1
    @36
    @4
    @29
    @6
    oveq2
    eqeq12d
    @39
    @35
    @20
    wcel
    #
    wa
    #
    @28
    @35
    cR
    cmulr
    cfv
    #
    co
    #
    @21
    cec
    #
    @35
    @28
    @42
    co
    #
    @21
    cec
    #
    @38
    @37
    @41
    @43
    @45
    @21
    @2
    @34
    @40
    @43
    @45
    wceq
    #
    @0
    @34
    @40
    @47
    @1
    @20
    cR
    @42
    @28
    @35
    @20
    eqid
    #
    @42
    eqid
    #
    crngcom
    3adant1r
    3expa
    eceq1d
    @2
    @34
    @40
    @38
    @44
    wceq
    @2
    @21
    cR
    @6
    @42
    cU
    @20
    @28
    @35
    crg
    vd
    vc
    va
    vb
    @25
    @26
    @2
    cS
    cR
    csubg
    cfv
    wcel
    #
    @20
    @21
    wer
    @0
    @11
    @1
    @50
    @14
    cR
    cI
    cS
    quscrng.i
    lidlsubg
    sylan
    @21
    cR
    @20
    cS
    @48
    @21
    eqid
    #
    eqger
    syl
    #
    @15
    @2
    @11
    @13
    va
    cv
    #
    vc
    cv
    #
    @21
    wbr
    vb
    cv
    #
    vd
    cv
    #
    @21
    wbr
    wa
    @53
    @55
    @42
    co
    @54
    @56
    @42
    co
    #
    @21
    wbr
    wi
    @15
    @16
    @53
    @55
    @54
    @56
    cR
    cS
    @42
    @21
    @12
    @20
    @48
    @51
    @17
    @49
    2idlcpbl
    syl2anc
    #
    @2
    @11
    @54
    @20
    wcel
    #
    @56
    @20
    wcel
    #
    wa
    @57
    @20
    wcel
    #
    @15
    @11
    @59
    @60
    @61
    @20
    cR
    @42
    @54
    @56
    @48
    @49
    ringcl
    3expb
    sylan
    #
    @49
    @6
    eqid
    #
    qusmulval
    3expa
    @2
    @40
    @34
    @37
    @46
    wceq
    #
    @2
    @40
    @34
    @64
    @2
    @21
    cR
    @6
    @42
    cU
    @20
    @35
    @28
    crg
    vd
    vc
    va
    vb
    @25
    @26
    @52
    @15
    @58
    @62
    @49
    @63
    qusmulval
    3expa
    an32s
    3eqtr4rd
    ectocld
    an32s
    ectocld
    expl
    sylbird
    ralrimivv
    vx
    vy
    @10
    cU
    @6
    @10
    eqid
    @63
    iscrng2
    sylanbrc
end
