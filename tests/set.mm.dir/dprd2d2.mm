include "cmpt2.mm"
include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "co.mm"
include "cmpt.mm"
include "wceq.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "csubg.mm"
include "cfv.mm"
include "cmrc.mm"
include "wrel.mm"
include "wral.mm"
include "relxp.mm"
include "rgenw.mm"
include "reliun.mm"
include "mpbir.mm"
include "a1i.mm"
include "wcel.mm"
include "wf.mm"
include "ralrimivva.mm"
include "eqid.mm"
include "fmpt2x.mm"
include "sylib.mm"
include "dmiun.mm"
include "wss.mm"
include "wa.mm"
include "dmxpss.mm"
include "simpr.mm"
include "snssd.mm"
include "syl5ss.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "syl5eqss.mm"
include "csb.mm"
include "cima.mm"
include "simprl.mm"
include "simprr.mm"
include "ovmpt4g.mm"
include "syl3anc.mm"
include "anassrs.mm"
include "mpteq2dva.mm"
include "breqtrrd.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfmpt21.mm"
include "nfov.mm"
include "nfmpt.mm"
include "nfbr.mm"
include "weq.mm"
include "csbeq1a.mm"
include "oveq1.mm"
include "mpteq12dv.mm"
include "breq2d.mm"
include "rspc.mm"
include "mpan9.mm"
include "nfmpt22.mm"
include "oveq2.mm"
include "cbvmpt.mm"
include "cop.mm"
include "wex.mm"
include "nfv.mm"
include "nfcri.mm"
include "nfan.mm"
include "eleq2d.mm"
include "anbi2d.mm"
include "equsexv.mm"
include "simplr.mm"
include "eqeltrd.mm"
include "biantrurd.mm"
include "pm5.32da.mm"
include "anass.mm"
include "eqcom.mm"
include "vex.mm"
include "opth.mm"
include "bitr2i.mm"
include "anbi1i.mm"
include "3bitr3g.mm"
include "exbidv.mm"
include "syl5bbr.mm"
include "eleq1.mm"
include "ceqsexv.mm"
include "excom.mm"
include "wb.mm"
include "elrelimasn.mm"
include "ax-mp.mm"
include "df-br.mm"
include "eliunxp.mm"
include "3bitri.mm"
include "syl6bbr.mm"
include "eqrdv.mm"
include "mpteq1d.mm"
include "syl5eq.mm"
include "breqtrd.mm"
include "oveq2d.mm"
include "dprd2da.mm"
include "dprd2db.mm"
include "eqtr3d.mm"
include "eqtrd.mm"
include "jca.mm"

theorem dprd2d2
  let wph: wff ph
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let cG: class G
  let cI: class I
  let cJ: class J
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume dprd2d2.1: |- ( ( ph /\ ( i e. I /\ j e. J ) ) -> S e. ( SubGrp ` G ) )
  assume dprd2d2.2: |- ( ( ph /\ i e. I ) -> G dom DProd ( j e. J |-> S ) )
  assume dprd2d2.3: |- ( ph -> G dom DProd ( i e. I |-> ( G DProd ( j e. J |-> S ) ) ) )

  disjoint i j
  disjoint G i
  disjoint G j
  disjoint I i
  disjoint I j
  disjoint J j
  disjoint i ph
  disjoint j ph
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint x y
  disjoint x z
  disjoint G x
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint S x
  disjoint S y
  disjoint S z
  assert |- ( ph -> ( G dom DProd ( i e. I , j e. J |-> S ) /\ ( G DProd ( i e. I , j e. J |-> S ) ) = ( G DProd ( i e. I |-> ( G DProd ( j e. J |-> S ) ) ) ) ) )

  proof
    wph
    cG
    vi
    vj
    cI
    cJ
    cS
    cmpt2
    #
    cdprd
    cdm
    #
    wbr
    cG
    @0
    cdprd
    co
    #
    cG
    vi
    cI
    cG
    vj
    cJ
    cS
    cmpt
    #
    cdprd
    co
    #
    cmpt
    #
    cdprd
    co
    #
    wceq
    wph
    vi
    cI
    vi
    cv
    #
    csn
    #
    cJ
    cxp
    #
    ciun
    #
    @0
    vx
    vy
    cG
    cI
    cG
    csubg
    cfv
    #
    cmrc
    cfv
    #
    @10
    wrel
    #
    wph
    @13
    @9
    wrel
    #
    vi
    cI
    wral
    @14
    vi
    cI
    @8
    cJ
    relxp
    rgenw
    vi
    cI
    @9
    reliun
    mpbir
    #
    a1i
    #
    wph
    cS
    @11
    wcel
    #
    vj
    cJ
    wral
    vi
    cI
    wral
    @10
    @11
    @0
    wf
    wph
    @17
    vi
    vj
    cI
    cJ
    dprd2d2.1
    ralrimivva
    vi
    vj
    cI
    cJ
    cS
    @11
    @0
    @0
    eqid
    #
    fmpt2x
    sylib
    #
    wph
    @10
    cdm
    vi
    cI
    @9
    cdm
    #
    ciun
    #
    cI
    vi
    cI
    @9
    dmiun
    wph
    @20
    cI
    wss
    #
    vi
    cI
    wral
    @21
    cI
    wss
    wph
    @22
    vi
    cI
    wph
    @7
    cI
    wcel
    #
    wa
    #
    @20
    @8
    cI
    @8
    cJ
    dmxpss
    @24
    @7
    cI
    wph
    @23
    simpr
    snssd
    syl5ss
    ralrimiva
    vi
    cI
    @20
    cI
    iunss
    sylibr
    syl5eqss
    #
    wph
    vx
    cv
    #
    cI
    wcel
    #
    wa
    #
    cG
    vj
    vi
    @26
    cJ
    csb
    #
    @26
    vj
    cv
    #
    @0
    co
    #
    cmpt
    #
    vy
    @10
    @26
    csn
    cima
    #
    @26
    vy
    cv
    #
    @0
    co
    #
    cmpt
    #
    @1
    wph
    cG
    vj
    cJ
    @7
    @30
    @0
    co
    #
    cmpt
    #
    @1
    wbr
    #
    vi
    cI
    wral
    @27
    cG
    @32
    @1
    wbr
    #
    wph
    @39
    vi
    cI
    @24
    cG
    @3
    @38
    @1
    dprd2d2.2
    @24
    vj
    cJ
    @37
    cS
    wph
    @23
    @30
    cJ
    wcel
    #
    @37
    cS
    wceq
    #
    wph
    @23
    @41
    wa
    #
    wa
    @23
    @41
    @17
    @42
    wph
    @23
    @41
    simprl
    wph
    @23
    @41
    simprr
    dprd2d2.1
    vi
    vj
    cI
    cJ
    cS
    @0
    @11
    @18
    ovmpt4g
    syl3anc
    anassrs
    mpteq2dva
    #
    breqtrrd
    ralrimiva
    @39
    @40
    vi
    @26
    cI
    vi
    cG
    @32
    @1
    vi
    cG
    nfcv
    #
    vi
    @1
    nfcv
    vi
    vj
    @29
    @31
    vi
    @26
    cJ
    nfcsb1v
    #
    vi
    @26
    @30
    @0
    vi
    @26
    nfcv
    vi
    vj
    cI
    cJ
    cS
    nfmpt21
    vi
    @30
    nfcv
    nfov
    nfmpt
    #
    nfbr
    vi
    vx
    weq
    #
    @38
    @32
    cG
    @1
    @48
    vj
    cJ
    @37
    @29
    @31
    vi
    @26
    cJ
    csbeq1a
    #
    @7
    @26
    @30
    @0
    oveq1
    mpteq12dv
    #
    breq2d
    rspc
    mpan9
    @28
    @32
    vy
    @29
    @35
    cmpt
    @36
    vj
    vy
    @29
    @31
    @35
    vy
    @31
    nfcv
    vj
    @26
    @34
    @0
    vj
    @26
    nfcv
    vi
    vj
    cI
    cJ
    cS
    nfmpt22
    vj
    @34
    nfcv
    nfov
    @30
    @34
    @26
    @0
    oveq2
    cbvmpt
    @28
    vy
    @29
    @33
    @35
    @28
    vz
    @29
    @33
    @28
    vz
    cv
    #
    @29
    wcel
    #
    @26
    @51
    cop
    #
    @7
    @30
    cop
    #
    wceq
    #
    @43
    wa
    #
    vj
    wex
    vi
    wex
    #
    @51
    @33
    wcel
    #
    @28
    vj
    vz
    weq
    #
    @30
    @29
    wcel
    #
    wa
    #
    vj
    wex
    @56
    vi
    wex
    #
    vj
    wex
    @52
    @57
    @28
    @61
    @62
    vj
    @61
    @48
    @59
    @41
    wa
    #
    wa
    #
    vi
    wex
    @28
    @62
    @63
    @61
    vi
    vx
    @59
    @60
    vi
    @59
    vi
    nfv
    vi
    vj
    @29
    @46
    nfcri
    nfan
    @48
    @41
    @60
    @59
    @48
    cJ
    @29
    @30
    @49
    eleq2d
    anbi2d
    equsexv
    @28
    @64
    @56
    vi
    @28
    @48
    @59
    wa
    #
    @41
    wa
    @65
    @43
    wa
    @64
    @56
    @28
    @65
    @41
    @43
    @28
    @65
    wa
    #
    @23
    @41
    @66
    @7
    @26
    cI
    @28
    @48
    @59
    simprl
    wph
    @27
    @65
    simplr
    eqeltrd
    biantrurd
    pm5.32da
    @48
    @59
    @41
    anass
    @65
    @55
    @43
    @55
    @54
    @53
    wceq
    @65
    @53
    @54
    eqcom
    @7
    @30
    @26
    @51
    vi
    vex
    vj
    vex
    opth
    bitr2i
    anbi1i
    3bitr3g
    exbidv
    syl5bbr
    exbidv
    @60
    @52
    vj
    @51
    vz
    vex
    @30
    @51
    @29
    eleq1
    ceqsexv
    @56
    vj
    vi
    excom
    3bitr3g
    @58
    @26
    @51
    @10
    wbr
    #
    @53
    @10
    wcel
    @57
    @13
    @58
    @67
    wb
    @15
    @26
    @51
    @10
    elrelimasn
    ax-mp
    @26
    @51
    @10
    df-br
    vi
    vj
    cI
    cJ
    @53
    eliunxp
    3bitri
    syl6bbr
    eqrdv
    mpteq1d
    syl5eq
    #
    breqtrd
    #
    wph
    cG
    vi
    cI
    cG
    @38
    cdprd
    co
    #
    cmpt
    #
    vx
    cI
    cG
    @36
    cdprd
    co
    #
    cmpt
    #
    @1
    wph
    cG
    @5
    @71
    @1
    dprd2d2.3
    wph
    vi
    cI
    @70
    @4
    @24
    @38
    @3
    cG
    cdprd
    @44
    oveq2d
    mpteq2dva
    #
    breqtrrd
    wph
    @71
    vx
    cI
    cG
    @32
    cdprd
    co
    #
    cmpt
    @73
    vi
    vx
    cI
    @70
    @75
    vx
    @70
    nfcv
    vi
    cG
    @32
    cdprd
    @45
    vi
    cdprd
    nfcv
    @47
    nfov
    @48
    @38
    @32
    cG
    cdprd
    @50
    oveq2d
    cbvmpt
    wph
    vx
    cI
    @75
    @72
    @28
    @32
    @36
    cG
    cdprd
    @68
    oveq2d
    mpteq2dva
    syl5eq
    #
    breqtrd
    #
    @12
    eqid
    #
    dprd2da
    wph
    @2
    cG
    @73
    cdprd
    co
    @6
    wph
    @10
    @0
    vx
    vy
    cG
    cI
    @12
    @16
    @19
    @25
    @69
    @77
    @78
    dprd2db
    wph
    @73
    @5
    cG
    cdprd
    wph
    @71
    @73
    @5
    @76
    @74
    eqtr3d
    oveq2d
    eqtrd
    jca
end
