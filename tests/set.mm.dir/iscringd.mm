include "cop.mm"
include "crngo.mm"
include "wcel.mm"
include "ccm2.mm"
include "ccring.mm"
include "cv.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "id.mm"
include "3com13.mm"
include "wa.mm"
include "wi.mm"
include "eleq1.mm"
include "3anbi1d.mm"
include "anbi2d.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "3anbi3d.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "cablo.mm"
include "crn.mm"
include "adantr.mm"
include "simpr3.mm"
include "eleqtrd.mm"
include "simpr2.mm"
include "eqid.mm"
include "ablocom.mm"
include "syl3anc.mm"
include "simpr1.mm"
include "cgr.mm"
include "ablogrpo.mm"
include "syl.mm"
include "grpocl.mm"
include "eleqtrrd.mm"
include "jca.mm"
include "ovex.mm"
include "chvarv.mm"
include "vtocl.mm"
include "syldan.mm"
include "3adantr3.mm"
include "3adantr2.mm"
include "cxp.mm"
include "wf.mm"
include "fovrnd.mm"
include "3eqtrd.mm"
include "3eqtr2d.mm"
include "sylan2.mm"
include "imbi2d.mm"
include "an12s.mm"
include "ex.mm"
include "vtoclga.mm"
include "mpcom.mm"
include "eqtrd.mm"
include "isrngod.mm"
include "wral.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "biimpar.mm"
include "ralrimivva.mm"
include "cvv.mm"
include "wb.mm"
include "rnexg.mm"
include "eqeltrd.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "fex.mm"
include "iscom2.mm"
include "mpbird.mm"
include "iscrngo.mm"
include "sylanbrc.mm"

theorem iscringd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cU: class U
  let cG: class G
  let cH: class H
  let cX: class X
  let vw: setvar w
  assume iscringd.1: |- ( ph -> G e. AbelOp )
  assume iscringd.2: |- ( ph -> X = ran G )
  assume iscringd.3: |- ( ph -> H : ( X X. X ) --> X )
  assume iscringd.4: |- ( ( ph /\ ( x e. X /\ y e. X /\ z e. X ) ) -> ( ( x H y ) H z ) = ( x H ( y H z ) ) )
  assume iscringd.5: |- ( ( ph /\ ( x e. X /\ y e. X /\ z e. X ) ) -> ( x H ( y G z ) ) = ( ( x H y ) G ( x H z ) ) )
  assume iscringd.6: |- ( ph -> U e. X )
  assume iscringd.7: |- ( ( ph /\ y e. X ) -> ( y H U ) = y )
  assume iscringd.8: |- ( ( ph /\ ( x e. X /\ y e. X ) ) -> ( x H y ) = ( y H x ) )

  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint U x
  disjoint U y
  disjoint ph w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint G w
  disjoint H w
  disjoint X w
  assert |- ( ph -> <. G , H >. e. CRingOps )

  proof
    wph
    cG
    cH
    cop
    #
    crngo
    wcel
    @0
    ccm2
    wcel
    #
    @0
    ccring
    wcel
    wph
    vx
    vy
    vz
    cU
    cG
    cH
    cX
    iscringd.1
    iscringd.2
    iscringd.3
    iscringd.4
    iscringd.5
    vx
    cv
    #
    cX
    wcel
    #
    vy
    cv
    #
    cX
    wcel
    #
    vz
    cv
    #
    cX
    wcel
    #
    w3a
    #
    wph
    @7
    @5
    @3
    w3a
    #
    @2
    @4
    cG
    co
    #
    @6
    cH
    co
    #
    @2
    @6
    cH
    co
    #
    @4
    @6
    cH
    co
    #
    cG
    co
    #
    wceq
    #
    @7
    @5
    @3
    @9
    @9
    id
    3com13
    wph
    vw
    cv
    #
    cX
    wcel
    #
    @5
    @3
    w3a
    #
    wa
    #
    @10
    @16
    cH
    co
    #
    @2
    @16
    cH
    co
    #
    @4
    @16
    cH
    co
    #
    cG
    co
    #
    wceq
    #
    wi
    #
    wph
    @9
    wa
    #
    @15
    wi
    vw
    vz
    @16
    @6
    wceq
    #
    @19
    @26
    @24
    @15
    @27
    @18
    @9
    wph
    @27
    @17
    @7
    @5
    @3
    @16
    @6
    cX
    eleq1
    3anbi1d
    anbi2d
    @27
    @20
    @11
    @23
    @14
    @16
    @6
    @10
    cH
    oveq2
    @27
    @21
    @12
    @22
    @13
    cG
    @16
    @6
    @2
    cH
    oveq2
    @16
    @6
    @4
    cH
    oveq2
    oveq12d
    eqeq12d
    imbi12d
    wph
    @17
    @5
    @7
    w3a
    #
    wa
    #
    @6
    @4
    cG
    co
    #
    @16
    cH
    co
    #
    @6
    @16
    cH
    co
    #
    @22
    cG
    co
    #
    wceq
    #
    wi
    #
    @25
    vz
    vx
    @6
    @2
    wceq
    #
    @29
    @19
    @34
    @24
    @36
    @28
    @18
    wph
    @36
    @7
    @3
    @17
    @5
    @6
    @2
    cX
    eleq1
    3anbi3d
    anbi2d
    @36
    @31
    @20
    @33
    @23
    @36
    @30
    @10
    @16
    cH
    @6
    @2
    @4
    cG
    oveq1
    oveq1d
    @36
    @32
    @21
    @22
    cG
    @6
    @2
    @16
    cH
    oveq1
    oveq1d
    eqeq12d
    imbi12d
    wph
    @8
    wa
    #
    @30
    @2
    cH
    co
    #
    @6
    @2
    cH
    co
    #
    @4
    @2
    cH
    co
    #
    cG
    co
    #
    wceq
    #
    wi
    @35
    vx
    vw
    @2
    @16
    wceq
    #
    @37
    @29
    @42
    @34
    @43
    @8
    @28
    wph
    @43
    @3
    @17
    @5
    @7
    @2
    @16
    cX
    eleq1
    3anbi1d
    anbi2d
    @43
    @38
    @31
    @41
    @33
    @2
    @16
    @30
    cH
    oveq2
    @43
    @39
    @32
    @40
    @22
    cG
    @2
    @16
    @6
    cH
    oveq2
    @2
    @16
    @4
    cH
    oveq2
    oveq12d
    eqeq12d
    imbi12d
    @37
    @38
    @4
    @6
    cG
    co
    #
    @2
    cH
    co
    #
    @2
    @44
    cH
    co
    #
    @41
    @37
    @30
    @44
    @2
    cH
    @37
    cG
    cablo
    wcel
    #
    @6
    cG
    crn
    #
    wcel
    #
    @4
    @48
    wcel
    #
    @30
    @44
    wceq
    wph
    @47
    @8
    iscringd.1
    adantr
    #
    @37
    @6
    cX
    @48
    wph
    @3
    @5
    @7
    simpr3
    #
    wph
    cX
    @48
    wceq
    @8
    iscringd.2
    adantr
    #
    eleqtrd
    #
    @37
    @4
    cX
    @48
    wph
    @3
    @5
    @7
    simpr2
    #
    @53
    eleqtrd
    #
    @6
    @4
    cG
    @48
    @48
    eqid
    #
    ablocom
    syl3anc
    oveq1d
    wph
    @8
    @3
    @44
    cX
    wcel
    #
    wa
    #
    @46
    @45
    wceq
    #
    @37
    @3
    @58
    wph
    @3
    @5
    @7
    simpr1
    #
    @37
    @44
    @48
    cX
    @37
    cG
    cgr
    wcel
    #
    @50
    @49
    @44
    @48
    wcel
    @37
    @47
    @62
    @51
    cG
    ablogrpo
    syl
    @56
    @54
    @4
    @6
    cG
    @48
    @57
    grpocl
    syl3anc
    @53
    eleqtrrd
    jca
    wph
    @3
    @17
    wa
    #
    wa
    #
    @21
    @16
    @2
    cH
    co
    #
    wceq
    #
    wi
    #
    wph
    @59
    wa
    #
    @60
    wi
    vw
    @44
    @4
    @6
    cG
    ovex
    @16
    @44
    wceq
    #
    @64
    @68
    @66
    @60
    @69
    @63
    @59
    wph
    @69
    @17
    @58
    @3
    @16
    @44
    cX
    eleq1
    anbi2d
    anbi2d
    @69
    @21
    @46
    @65
    @45
    @16
    @44
    @2
    cH
    oveq2
    @16
    @44
    @2
    cH
    oveq1
    eqeq12d
    imbi12d
    wph
    @3
    @5
    wa
    #
    wa
    #
    @2
    @4
    cH
    co
    #
    @40
    wceq
    #
    wi
    #
    @67
    vy
    vw
    @4
    @16
    wceq
    #
    @71
    @64
    @73
    @66
    @75
    @70
    @63
    wph
    @75
    @5
    @17
    @3
    @4
    @16
    cX
    eleq1
    anbi2d
    anbi2d
    @75
    @72
    @21
    @40
    @65
    @4
    @16
    @2
    cH
    oveq2
    @4
    @16
    @2
    cH
    oveq1
    eqeq12d
    imbi12d
    iscringd.8
    chvarv
    vtocl
    syldan
    @37
    @46
    @72
    @12
    cG
    co
    @40
    @39
    cG
    co
    #
    @41
    iscringd.5
    @37
    @72
    @40
    @12
    @39
    cG
    wph
    @3
    @5
    @73
    @7
    iscringd.8
    3adantr3
    wph
    @3
    @7
    @12
    @39
    wceq
    #
    @5
    @74
    wph
    @3
    @7
    wa
    #
    wa
    #
    @77
    wi
    vy
    vz
    @4
    @6
    wceq
    #
    @71
    @79
    @73
    @77
    @80
    @70
    @78
    wph
    @80
    @5
    @7
    @3
    @4
    @6
    cX
    eleq1
    anbi2d
    anbi2d
    @80
    @72
    @12
    @40
    @39
    @4
    @6
    @2
    cH
    oveq2
    @4
    @6
    @2
    cH
    oveq1
    eqeq12d
    imbi12d
    iscringd.8
    chvarv
    3adantr2
    oveq12d
    @37
    @47
    @40
    @48
    wcel
    @39
    @48
    wcel
    @76
    @41
    wceq
    @51
    @37
    @40
    cX
    @48
    @37
    @4
    @2
    cX
    cX
    cX
    cH
    wph
    cX
    cX
    cxp
    #
    cX
    cH
    wf
    #
    @8
    iscringd.3
    adantr
    #
    @55
    @61
    fovrnd
    @53
    eleqtrd
    @37
    @39
    cX
    @48
    @37
    @6
    @2
    cX
    cX
    cX
    cH
    @83
    @52
    @61
    fovrnd
    @53
    eleqtrd
    @40
    @39
    cG
    @48
    @57
    ablocom
    syl3anc
    3eqtrd
    3eqtr2d
    chvarv
    chvarv
    chvarv
    sylan2
    iscringd.6
    wph
    @5
    wa
    #
    cU
    @4
    cH
    co
    #
    @4
    cU
    cH
    co
    #
    @4
    cU
    cX
    wcel
    #
    @84
    @85
    @86
    wceq
    #
    wph
    @87
    @5
    iscringd.6
    adantr
    @84
    @73
    wi
    @84
    @88
    wi
    vx
    cU
    cX
    @2
    cU
    wceq
    #
    @73
    @88
    @84
    @89
    @72
    @85
    @40
    @86
    @2
    cU
    @4
    cH
    oveq1
    @2
    cU
    @4
    cH
    oveq2
    eqeq12d
    imbi2d
    @3
    @84
    @73
    wph
    @3
    @5
    @73
    iscringd.8
    an12s
    ex
    vtoclga
    mpcom
    iscringd.7
    eqtrd
    iscringd.7
    isrngod
    wph
    @1
    @73
    vy
    @48
    wral
    vx
    @48
    wral
    #
    wph
    @73
    vx
    vy
    @48
    @48
    wph
    @2
    @48
    wcel
    #
    @50
    wa
    #
    @70
    @73
    wph
    @70
    @92
    wph
    @3
    @91
    @5
    @50
    wph
    cX
    @48
    @2
    iscringd.2
    eleq2d
    wph
    cX
    @48
    @4
    iscringd.2
    eleq2d
    anbi12d
    biimpar
    iscringd.8
    syldan
    ralrimivva
    wph
    @47
    cH
    cvv
    wcel
    #
    @1
    @90
    wb
    iscringd.1
    wph
    @82
    @81
    cvv
    wcel
    #
    @93
    iscringd.3
    wph
    cX
    cvv
    wcel
    #
    @95
    @94
    wph
    cX
    @48
    cvv
    iscringd.2
    wph
    @47
    @48
    cvv
    wcel
    iscringd.1
    cG
    cablo
    rnexg
    syl
    eqeltrd
    #
    @96
    cX
    cX
    cvv
    cvv
    xpexg
    syl2anc
    @81
    cX
    cvv
    cH
    fex
    syl2anc
    cablo
    cvv
    cG
    cH
    vx
    vy
    iscom2
    syl2anc
    mpbird
    @0
    iscrngo
    sylanbrc
end
