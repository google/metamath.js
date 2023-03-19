include "cbs.mm"
include "cfv.mm"
include "cplusg.mm"
include "c0g.mm"
include "ccom.mm"
include "eqidd.mm"
include "cv.mm"
include "wcel.mm"
include "co.mm"
include "wa.mm"
include "cvv.mm"
include "eqid.mm"
include "elex.mm"
include "syl.mm"
include "adantr.mm"
include "cmnd.mm"
include "wf.mm"
include "simprl.mm"
include "simprr.mm"
include "prdsplusgcl.mm"
include "3impb.mm"
include "w3a.mm"
include "cmpt.mm"
include "wceq.mm"
include "ffvelrnda.mm"
include "adantlr.mm"
include "ad2antrr.mm"
include "wfn.mm"
include "ffn.mm"
include "simplr1.mm"
include "simpr.mm"
include "prdsbasprj.mm"
include "simplr2.mm"
include "simplr3.mm"
include "mndass.mm"
include "syl13anc.mm"
include "prdsplusgfval.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "mpteq2dva.mm"
include "3adantr3.mm"
include "simpr3.mm"
include "prdsplusgval.mm"
include "simpr1.mm"
include "simpr2.mm"
include "wral.mm"
include "prdsidlem.mm"
include "simpld.mm"
include "simprd.mm"
include "r19.21bi.mm"
include "ismndd.mm"

theorem prdsmndd
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vy: setvar y
  let vc: setvar c
  assume prdsmndd.y: |- Y = ( S Xs_ R )
  assume prdsmndd.i: |- ( ph -> I e. W )
  assume prdsmndd.s: |- ( ph -> S e. V )
  assume prdsmndd.r: |- ( ph -> R : I --> Mnd )


  assert |- ( ph -> Y e. Mnd )

  proof
    wph
    va
    vb
    vc
    cY
    cbs
    cfv
    #
    cY
    cplusg
    cfv
    #
    cY
    c0g
    cR
    ccom
    #
    wph
    @0
    eqidd
    wph
    @1
    eqidd
    wph
    va
    cv
    #
    @0
    wcel
    #
    vb
    cv
    #
    @0
    wcel
    #
    @3
    @5
    @1
    co
    #
    @0
    wcel
    #
    wph
    @4
    @6
    wa
    #
    wa
    @0
    @1
    cR
    cS
    @3
    @5
    cI
    cvv
    cvv
    cY
    prdsmndd.y
    @0
    eqid
    #
    @1
    eqid
    #
    wph
    cS
    cvv
    wcel
    #
    @9
    wph
    cS
    cV
    wcel
    @12
    prdsmndd.s
    cS
    cV
    elex
    syl
    #
    adantr
    wph
    cI
    cvv
    wcel
    #
    @9
    wph
    cI
    cW
    wcel
    @14
    prdsmndd.i
    cI
    cW
    elex
    syl
    #
    adantr
    wph
    cI
    cmnd
    cR
    wf
    #
    @9
    prdsmndd.r
    adantr
    wph
    @4
    @6
    simprl
    wph
    @4
    @6
    simprr
    prdsplusgcl
    #
    3impb
    wph
    @4
    @6
    vc
    cv
    #
    @0
    wcel
    #
    w3a
    #
    wa
    #
    vy
    cI
    vy
    cv
    #
    @7
    cfv
    #
    @22
    @18
    cfv
    #
    @22
    cR
    cfv
    #
    cplusg
    cfv
    #
    co
    #
    cmpt
    vy
    cI
    @22
    @3
    cfv
    #
    @22
    @5
    @18
    @1
    co
    #
    cfv
    #
    @26
    co
    #
    cmpt
    @7
    @18
    @1
    co
    @3
    @29
    @1
    co
    @21
    vy
    cI
    @27
    @31
    @21
    @22
    cI
    wcel
    #
    wa
    #
    @28
    @22
    @5
    cfv
    #
    @26
    co
    #
    @24
    @26
    co
    #
    @28
    @34
    @24
    @26
    co
    #
    @26
    co
    #
    @27
    @31
    @33
    @25
    cmnd
    wcel
    #
    @28
    @25
    cbs
    cfv
    #
    wcel
    @34
    @40
    wcel
    @24
    @40
    wcel
    @36
    @38
    wceq
    wph
    @32
    @39
    @20
    wph
    cI
    cmnd
    @22
    cR
    prdsmndd.r
    ffvelrnda
    adantlr
    @33
    @0
    cR
    cS
    @3
    cI
    @22
    cvv
    cvv
    cY
    prdsmndd.y
    @10
    wph
    @12
    @20
    @32
    @13
    ad2antrr
    #
    wph
    @14
    @20
    @32
    @15
    ad2antrr
    #
    wph
    cR
    cI
    wfn
    #
    @20
    @32
    wph
    @16
    @43
    prdsmndd.r
    cI
    cmnd
    cR
    ffn
    syl
    #
    ad2antrr
    #
    @4
    @6
    @19
    wph
    @32
    simplr1
    #
    @21
    @32
    simpr
    #
    prdsbasprj
    @33
    @0
    cR
    cS
    @5
    cI
    @22
    cvv
    cvv
    cY
    prdsmndd.y
    @10
    @41
    @42
    @45
    @4
    @6
    @19
    wph
    @32
    simplr2
    #
    @47
    prdsbasprj
    @33
    @0
    cR
    cS
    @18
    cI
    @22
    cvv
    cvv
    cY
    prdsmndd.y
    @10
    @41
    @42
    @45
    @4
    @6
    @19
    wph
    @32
    simplr3
    #
    @47
    prdsbasprj
    @40
    @26
    @25
    @28
    @34
    @24
    @40
    eqid
    @26
    eqid
    mndass
    syl13anc
    @33
    @23
    @35
    @24
    @26
    @33
    @0
    @1
    cR
    cS
    @3
    @5
    cI
    @22
    cvv
    cvv
    cY
    prdsmndd.y
    @10
    @41
    @42
    @45
    @46
    @48
    @11
    @47
    prdsplusgfval
    oveq1d
    @33
    @30
    @37
    @28
    @26
    @33
    @0
    @1
    cR
    cS
    @5
    @18
    cI
    @22
    cvv
    cvv
    cY
    prdsmndd.y
    @10
    @41
    @42
    @45
    @48
    @49
    @11
    @47
    prdsplusgfval
    oveq2d
    3eqtr4d
    mpteq2dva
    @21
    vy
    @0
    @1
    cR
    cS
    @7
    @18
    cI
    cvv
    cvv
    cY
    prdsmndd.y
    @10
    wph
    @12
    @20
    @13
    adantr
    #
    wph
    @14
    @20
    @15
    adantr
    #
    wph
    @43
    @20
    @44
    adantr
    #
    wph
    @4
    @6
    @8
    @19
    @17
    3adantr3
    wph
    @4
    @6
    @19
    simpr3
    #
    @11
    prdsplusgval
    @21
    vy
    @0
    @1
    cR
    cS
    @3
    @29
    cI
    cvv
    cvv
    cY
    prdsmndd.y
    @10
    @50
    @51
    @52
    wph
    @4
    @6
    @19
    simpr1
    @21
    @0
    @1
    cR
    cS
    @5
    @18
    cI
    cvv
    cvv
    cY
    prdsmndd.y
    @10
    @11
    @50
    @51
    wph
    @16
    @20
    prdsmndd.r
    adantr
    wph
    @4
    @6
    @19
    simpr2
    @53
    prdsplusgcl
    @11
    prdsplusgval
    3eqtr4d
    wph
    @2
    @0
    wcel
    #
    @2
    @3
    @1
    co
    @3
    wceq
    #
    @3
    @2
    @1
    co
    @3
    wceq
    #
    wa
    #
    va
    @0
    wral
    #
    wph
    va
    @0
    @1
    cR
    cS
    cI
    cvv
    cvv
    cY
    @2
    prdsmndd.y
    @10
    @11
    @13
    @15
    prdsmndd.r
    @2
    eqid
    prdsidlem
    #
    simpld
    wph
    @4
    wa
    #
    @55
    @56
    wph
    @57
    va
    @0
    wph
    @54
    @58
    @59
    simprd
    r19.21bi
    #
    simpld
    @60
    @55
    @56
    @61
    simprd
    ismndd
end
