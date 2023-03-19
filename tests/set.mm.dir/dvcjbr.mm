include "cr.mm"
include "cdv.mm"
include "co.mm"
include "cfv.mm"
include "ccj.mm"
include "ccom.mm"
include "wbr.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cnt.mm"
include "wcel.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "cmin.mm"
include "cdiv.mm"
include "cmpt.mm"
include "climc.mm"
include "cdm.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cc.mm"
include "wss.mm"
include "ax-resscn.mm"
include "a1i.mm"
include "eqid.mm"
include "tgioo2.mm"
include "dvbssntr.mm"
include "sseldd.mm"
include "syl6ss.mm"
include "wf.mm"
include "wa.mm"
include "simpl.mm"
include "simpr.mm"
include "dvbss.mm"
include "syl2anc.mm"
include "dvlem.mm"
include "fmptd.mm"
include "ssid.mm"
include "crest.mm"
include "ctopon.mm"
include "wceq.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "restid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "wfun.mm"
include "wb.mm"
include "dvf.mm"
include "ffun.mm"
include "funfvbrb.mm"
include "mp2b.mm"
include "sylib.mm"
include "eldv.mm"
include "mpbid.mm"
include "simprd.mm"
include "ccn.mm"
include "ccnp.mm"
include "ccncf.mm"
include "cjcncf.mm"
include "cncfcn1.mm"
include "eleqtri.mm"
include "ffvelrni.mm"
include "syl.mm"
include "cncnpi.mm"
include "sylancr.mm"
include "limccnp.mm"
include "eqidd.mm"
include "cjf.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fmptco.mm"
include "adantr.mm"
include "eldifi.mm"
include "adantl.mm"
include "ffvelrnd.mm"
include "subcld.mm"
include "sselda.mm"
include "sylan2.mm"
include "resubcld.mm"
include "recnd.mm"
include "wne.mm"
include "eldifsni.mm"
include "subne0d.mm"
include "cjdivd.mm"
include "cjsub.mm"
include "fvco3.mm"
include "syl2an.mm"
include "oveq12d.mm"
include "eqtr4d.mm"
include "cjred.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "oveq1d.mm"
include "eleqtrd.mm"
include "fco.mm"
include "mpbir2and.mm"

theorem dvcjbr
  let wph: wff ph
  let cC: class C
  let cF: class F
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume dvcj.f: |- ( ph -> F : X --> CC )
  assume dvcj.x: |- ( ph -> X C_ RR )
  assume dvcj.c: |- ( ph -> C e. dom ( RR _D F ) )


  assert |- ( ph -> C ( RR _D ( * o. F ) ) ( * ` ( ( RR _D F ) ` C ) ) )

  proof
    wph
    cC
    cC
    cr
    cF
    cdv
    co
    #
    cfv
    #
    ccj
    cfv
    #
    cr
    ccj
    cF
    ccom
    #
    cdv
    co
    wbr
    cC
    cX
    cioo
    crn
    ctg
    cfv
    #
    cnt
    cfv
    cfv
    #
    wcel
    #
    @2
    vx
    cX
    cC
    csn
    #
    cdif
    #
    vx
    cv
    #
    @3
    cfv
    #
    cC
    @3
    cfv
    #
    cmin
    co
    #
    @9
    cC
    cmin
    co
    #
    cdiv
    co
    #
    cmpt
    #
    cC
    climc
    co
    #
    wcel
    wph
    @0
    cdm
    #
    @5
    cC
    wph
    cX
    cr
    cF
    @4
    ccnfld
    ctopn
    cfv
    #
    cr
    cc
    wss
    #
    wph
    ax-resscn
    a1i
    #
    dvcj.f
    dvcj.x
    @18
    @18
    eqid
    #
    tgioo2
    #
    @21
    dvbssntr
    dvcj.c
    sseldd
    wph
    @2
    ccj
    vx
    @8
    @9
    cF
    cfv
    #
    cC
    cF
    cfv
    #
    cmin
    co
    #
    @13
    cdiv
    co
    #
    cmpt
    #
    ccom
    #
    cC
    climc
    co
    @16
    wph
    @8
    cC
    @1
    cc
    @27
    ccj
    @18
    @18
    wph
    vx
    @8
    @26
    cc
    @27
    wph
    @9
    cC
    cX
    cF
    dvcj.f
    wph
    cX
    cr
    cc
    dvcj.x
    ax-resscn
    syl6ss
    wph
    @17
    cX
    cC
    wph
    cX
    cc
    cF
    wf
    #
    cX
    cr
    wss
    #
    @17
    cX
    wss
    dvcj.f
    dvcj.x
    @29
    @30
    wa
    #
    cX
    cr
    cF
    @19
    @31
    ax-resscn
    a1i
    @29
    @30
    simpl
    @29
    @30
    simpr
    dvbss
    syl2anc
    dvcj.c
    sseldd
    #
    dvlem
    #
    @27
    eqid
    #
    fmptd
    cc
    cc
    wss
    wph
    cc
    ssid
    a1i
    @21
    @18
    cc
    crest
    co
    #
    @18
    @18
    cc
    ctopon
    cfv
    #
    wcel
    @35
    @18
    wceq
    @18
    @21
    cnfldtopon
    #
    @18
    @36
    cc
    cc
    @18
    @37
    toponunii
    #
    restid
    ax-mp
    eqcomi
    wph
    @6
    @1
    @27
    cC
    climc
    co
    wcel
    #
    wph
    cC
    @1
    @0
    wbr
    #
    @6
    @39
    wa
    wph
    cC
    @17
    wcel
    #
    @40
    dvcj.c
    @17
    cc
    @0
    wf
    @0
    wfun
    @41
    @40
    wb
    cF
    dvf
    #
    @17
    cc
    @0
    ffun
    cC
    @0
    funfvbrb
    mp2b
    sylib
    wph
    vx
    cX
    cC
    @1
    cr
    @4
    cF
    @27
    @18
    @22
    @21
    @34
    @20
    dvcj.f
    dvcj.x
    eldv
    mpbid
    simprd
    wph
    ccj
    @18
    @18
    ccn
    co
    #
    wcel
    @1
    cc
    wcel
    #
    ccj
    @1
    @18
    @18
    ccnp
    co
    cfv
    wcel
    ccj
    cc
    cc
    ccncf
    co
    @43
    cjcncf
    @18
    @21
    cncfcn1
    eleqtri
    wph
    @41
    @44
    dvcj.c
    @17
    cc
    cC
    @0
    @42
    ffvelrni
    syl
    @1
    ccj
    @18
    @18
    cc
    @38
    cncnpi
    sylancr
    limccnp
    wph
    @28
    @15
    cC
    climc
    wph
    @28
    vx
    @8
    @26
    ccj
    cfv
    #
    cmpt
    @15
    wph
    vx
    vy
    @8
    cc
    @26
    vy
    cv
    #
    ccj
    cfv
    @45
    @27
    ccj
    @33
    wph
    @27
    eqidd
    wph
    vy
    cc
    cc
    ccj
    cc
    cc
    ccj
    wf
    #
    wph
    cjf
    a1i
    feqmptd
    @46
    @26
    ccj
    fveq2
    fmptco
    wph
    vx
    @8
    @45
    @14
    wph
    @9
    @8
    wcel
    #
    wa
    #
    @45
    @25
    ccj
    cfv
    #
    @13
    ccj
    cfv
    #
    cdiv
    co
    @14
    @49
    @25
    @13
    @49
    @23
    @24
    @49
    cX
    cc
    @9
    cF
    wph
    @29
    @48
    dvcj.f
    adantr
    @48
    @9
    cX
    wcel
    #
    wph
    @9
    cX
    @7
    eldifi
    #
    adantl
    ffvelrnd
    #
    wph
    @24
    cc
    wcel
    #
    @48
    wph
    cX
    cc
    cC
    cF
    dvcj.f
    @32
    ffvelrnd
    adantr
    #
    subcld
    @49
    @13
    @49
    @9
    cC
    @48
    wph
    @52
    @9
    cr
    wcel
    @53
    wph
    cX
    cr
    @9
    dvcj.x
    sselda
    sylan2
    #
    wph
    cC
    cr
    wcel
    @48
    wph
    cX
    cr
    cC
    dvcj.x
    @32
    sseldd
    adantr
    #
    resubcld
    #
    recnd
    @49
    @9
    cC
    @49
    @9
    @57
    recnd
    @49
    cC
    @58
    recnd
    @48
    @9
    cC
    wne
    wph
    @9
    cX
    cC
    eldifsni
    adantl
    subne0d
    cjdivd
    @49
    @50
    @12
    @51
    @13
    cdiv
    @49
    @50
    @23
    ccj
    cfv
    #
    @24
    ccj
    cfv
    #
    cmin
    co
    #
    @12
    @49
    @23
    cc
    wcel
    @55
    @50
    @62
    wceq
    @54
    @56
    @23
    @24
    cjsub
    syl2anc
    @49
    @10
    @60
    @11
    @61
    cmin
    wph
    @29
    @52
    @10
    @60
    wceq
    @48
    dvcj.f
    @53
    cX
    cc
    @9
    ccj
    cF
    fvco3
    syl2an
    wph
    @11
    @61
    wceq
    #
    @48
    wph
    @29
    cC
    cX
    wcel
    @63
    dvcj.f
    @32
    cX
    cc
    cC
    ccj
    cF
    fvco3
    syl2anc
    adantr
    oveq12d
    eqtr4d
    @49
    @13
    @59
    cjred
    oveq12d
    eqtrd
    mpteq2dva
    eqtrd
    oveq1d
    eleqtrd
    wph
    vx
    cX
    cC
    @2
    cr
    @4
    @3
    @15
    @18
    @22
    @21
    @15
    eqid
    @20
    wph
    @47
    @29
    cX
    cc
    @3
    wf
    cjf
    dvcj.f
    cX
    cc
    cc
    ccj
    cF
    fco
    sylancr
    dvcj.x
    eldv
    mpbir2and
end
