include "wcel.mm"
include "csn.mm"
include "wbr.mm"
include "wa.mm"
include "clvec.mm"
include "adantr.mm"
include "simpr.mm"
include "lsatcv0.mm"
include "cv.mm"
include "clspn.mm"
include "cfv.mm"
include "wceq.mm"
include "cbs.mm"
include "cdif.mm"
include "wrex.mm"
include "wn.mm"
include "wex.mm"
include "wpss.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "lsssn0.mm"
include "lcvpss.mm"
include "pssnel.mm"
include "wne.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "eqid.mm"
include "lssel.mm"
include "syl2anc.mm"
include "velsn.mm"
include "biimpri.mm"
include "necon3bi.mm"
include "adantl.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "jca.mm"
include "ex.mm"
include "eximdv.mm"
include "df-rex.mm"
include "syl6ibr.mm"
include "mpd.mm"
include "simpllr.mm"
include "wss.mm"
include "wi.mm"
include "wral.mm"
include "wb.mm"
include "lcvbr2.mm"
include "eldifi.mm"
include "lspsncl.mm"
include "lss0ss.mm"
include "eldifsni.mm"
include "lspsneq0.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "necomd.mm"
include "df-pss.mm"
include "simplr.mm"
include "lspsnel5a.mm"
include "psseq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "mpid.mm"
include "expimpd.mm"
include "sylbid.mm"
include "eqcomd.mm"
include "reximdva.mm"
include "islsat.mm"
include "impbida.mm"

theorem lsat0cv
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cS: class S
  let cU: class U
  let cW: class W
  let c.0: class .0.
  let vx: setvar x
  let vs: setvar s
  assume lsat0cv.o: |- .0. = ( 0g ` W )
  assume lsat0cv.s: |- S = ( LSubSp ` W )
  assume lsat0cv.a: |- A = ( LSAtoms ` W )
  assume lsat0cv.c: |- C = ( <oL ` W )
  assume lsat0cv.w: |- ( ph -> W e. LVec )
  assume lsat0cv.u: |- ( ph -> U e. S )


  assert |- ( ph -> ( U e. A <-> { .0. } C U ) )

  proof
    wph
    cU
    cA
    wcel
    #
    c.0
    csn
    #
    cU
    cC
    wbr
    #
    wph
    @0
    wa
    cA
    cC
    cU
    cW
    c.0
    lsat0cv.o
    lsat0cv.a
    lsat0cv.c
    wph
    cW
    clvec
    wcel
    #
    @0
    lsat0cv.w
    adantr
    wph
    @0
    simpr
    lsatcv0
    wph
    @2
    wa
    #
    @0
    cU
    vx
    cv
    #
    csn
    cW
    clspn
    cfv
    #
    cfv
    #
    wceq
    #
    vx
    cW
    cbs
    cfv
    #
    @1
    cdif
    #
    wrex
    #
    @4
    @5
    cU
    wcel
    #
    vx
    @10
    wrex
    #
    @11
    @4
    @12
    @5
    @1
    wcel
    #
    wn
    #
    wa
    #
    vx
    wex
    #
    @13
    @4
    @1
    cU
    wpss
    #
    @17
    @4
    cC
    cS
    @1
    cU
    cW
    clmod
    lsat0cv.s
    lsat0cv.c
    wph
    cW
    clmod
    wcel
    #
    @2
    wph
    @3
    @19
    lsat0cv.w
    cW
    lveclmod
    syl
    #
    adantr
    wph
    @1
    cS
    wcel
    #
    @2
    wph
    @19
    @21
    @20
    cS
    cW
    c.0
    lsat0cv.o
    lsat0cv.s
    lsssn0
    syl
    #
    adantr
    wph
    cU
    cS
    wcel
    #
    @2
    lsat0cv.u
    adantr
    wph
    @2
    simpr
    lcvpss
    vx
    @1
    cU
    pssnel
    syl
    @4
    @17
    @5
    @10
    wcel
    #
    @12
    wa
    #
    vx
    wex
    @13
    @4
    @16
    @25
    vx
    @4
    @16
    @25
    @4
    @16
    wa
    #
    @24
    @12
    @26
    @5
    @9
    wcel
    #
    @5
    c.0
    wne
    #
    @24
    @26
    @23
    @12
    @27
    wph
    @23
    @2
    @16
    lsat0cv.u
    ad2antrr
    @4
    @12
    @15
    simprl
    #
    cS
    cU
    @9
    cW
    @5
    @9
    eqid
    #
    lsat0cv.s
    lssel
    syl2anc
    @16
    @28
    @4
    @15
    @28
    @12
    @14
    @5
    c.0
    @14
    @5
    c.0
    wceq
    #
    vx
    c.0
    velsn
    biimpri
    necon3bi
    adantl
    adantl
    @5
    @9
    c.0
    eldifsn
    sylanbrc
    @29
    jca
    ex
    eximdv
    @12
    vx
    @10
    df-rex
    syl6ibr
    mpd
    @4
    @12
    @8
    vx
    @10
    @4
    @24
    wa
    #
    @12
    @8
    @32
    @12
    wa
    #
    @7
    cU
    @33
    @2
    @7
    cU
    wceq
    #
    wph
    @2
    @24
    @12
    simpllr
    @33
    @2
    @18
    @1
    vs
    cv
    #
    wpss
    #
    @35
    cU
    wss
    #
    wa
    #
    @35
    cU
    wceq
    #
    wi
    #
    vs
    cS
    wral
    #
    wa
    #
    @34
    @4
    @2
    @42
    wb
    #
    @24
    @12
    wph
    @43
    @2
    wph
    cC
    cS
    @1
    cU
    cW
    clvec
    vs
    lsat0cv.s
    lsat0cv.c
    lsat0cv.w
    @22
    lsat0cv.u
    lcvbr2
    adantr
    ad2antrr
    @33
    @18
    @41
    @34
    @33
    @18
    wa
    #
    @41
    @1
    @7
    wpss
    #
    @7
    cU
    wss
    #
    wa
    #
    @34
    @44
    @45
    @46
    @44
    @1
    @7
    wss
    #
    @1
    @7
    wne
    @45
    @44
    @19
    @7
    cS
    wcel
    #
    @48
    @32
    @19
    @12
    @18
    wph
    @19
    @2
    @24
    @20
    ad2antrr
    ad2antrr
    #
    @44
    @19
    @27
    @49
    @50
    @32
    @27
    @12
    @18
    @24
    @27
    @4
    @5
    @9
    @1
    eldifi
    adantl
    ad2antrr
    #
    cS
    @6
    @9
    cW
    @5
    @30
    lsat0cv.s
    @6
    eqid
    #
    lspsncl
    syl2anc
    #
    cS
    cW
    @7
    c.0
    lsat0cv.o
    lsat0cv.s
    lss0ss
    syl2anc
    @44
    @7
    @1
    @44
    @7
    @1
    wne
    @28
    @32
    @28
    @12
    @18
    @24
    @28
    @4
    @5
    @9
    c.0
    eldifsni
    adantl
    ad2antrr
    @44
    @7
    @1
    @5
    c.0
    @44
    @19
    @27
    @7
    @1
    wceq
    @31
    wb
    @50
    @51
    @6
    @9
    cW
    @5
    c.0
    @30
    lsat0cv.o
    @52
    lspsneq0
    syl2anc
    necon3bid
    mpbird
    necomd
    @1
    @7
    df-pss
    sylanbrc
    @44
    cS
    cU
    @6
    cW
    @5
    lsat0cv.s
    @52
    @50
    @32
    @23
    @12
    @18
    wph
    @23
    @2
    @24
    lsat0cv.u
    ad2antrr
    ad2antrr
    @32
    @12
    @18
    simplr
    lspsnel5a
    jca
    @44
    @49
    @41
    @47
    @34
    wi
    #
    wi
    @53
    @40
    @54
    vs
    @7
    cS
    @35
    @7
    wceq
    #
    @38
    @47
    @39
    @34
    @55
    @36
    @45
    @37
    @46
    @35
    @7
    @1
    psseq2
    @35
    @7
    cU
    sseq1
    anbi12d
    @35
    @7
    cU
    eqeq1
    imbi12d
    rspcv
    syl
    mpid
    expimpd
    sylbid
    mpd
    eqcomd
    ex
    reximdva
    mpd
    @4
    @3
    @0
    @11
    wb
    wph
    @3
    @2
    lsat0cv.w
    adantr
    vx
    cA
    cU
    @6
    @9
    cW
    clvec
    c.0
    @30
    @52
    lsat0cv.o
    lsat0cv.a
    islsat
    syl
    mpbird
    impbida
end
