include "cucn.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "cust.mm"
include "wb.mm"
include "isucn.mm"
include "syl2anc.mm"
include "wss.mm"
include "cxp.mm"
include "cfg.mm"
include "cfbas.mm"
include "ssfg.mm"
include "syl.mm"
include "syl6sseqr.mm"
include "adantr.mm"
include "sselda.mm"
include "simplr.mm"
include "wceq.mm"
include "breq.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "rexralbidv.mm"
include "rspcva.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "elfg.mm"
include "simplbda.mm"
include "syldan.mm"
include "ssbr.mm"
include "imim1d.mm"
include "adantl.mm"
include "ralrimivw.mm"
include "ralim.mm"
include "ralimi.mm"
include "3syl.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"
include "r19.37v.mm"
include "rexlimdva.mm"
include "ad3antrrr.mm"
include "ralrimiva.mm"
include "ssrexv.mm"
include "imbi1d.mm"
include "2ralbidv.mm"
include "cbvrexv.mm"
include "syl6ib.mm"
include "ralimdv.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "simp-4r.mm"
include "rspa.mm"
include "simp-4l.mm"
include "imim2d.mm"
include "reximdv.mm"
include "syl21anc.mm"
include "r19.29af.mm"
include "syld.mm"
include "imp.mm"
include "impbida.mm"
include "pm5.32da.mm"
include "bitrd.mm"

theorem isucn2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cS: class S
  let cU: class U
  let cF: class F
  let cV: class V
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vr: setvar r
  let vu: setvar u
  let vv: setvar v
  assume isucn2.u: |- U = ( ( X X. X ) filGen R )
  assume isucn2.v: |- V = ( ( Y X. Y ) filGen S )
  assume isucn2.1: |- ( ph -> U e. ( UnifOn ` X ) )
  assume isucn2.2: |- ( ph -> V e. ( UnifOn ` Y ) )
  assume isucn2.3: |- ( ph -> R e. ( fBas ` ( X X. X ) ) )
  assume isucn2.4: |- ( ph -> S e. ( fBas ` ( Y X. Y ) ) )

  disjoint r s
  disjoint r x
  disjoint r y
  disjoint F r
  disjoint s x
  disjoint s y
  disjoint F s
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint R r
  disjoint R x
  disjoint R y
  disjoint S s
  disjoint S x
  disjoint S y
  disjoint U r
  disjoint U s
  disjoint U x
  disjoint U y
  disjoint V s
  disjoint V x
  disjoint X r
  disjoint X s
  disjoint X x
  disjoint X y
  disjoint Y s
  disjoint Y x
  disjoint Y y
  disjoint ph r
  disjoint ph s
  disjoint ph x
  disjoint ph y
  disjoint r u
  disjoint r v
  disjoint s u
  disjoint s v
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint F u
  disjoint v x
  disjoint v y
  disjoint F v
  disjoint R u
  disjoint S u
  disjoint S v
  disjoint U u
  disjoint U v
  disjoint V u
  disjoint V v
  disjoint X u
  disjoint X v
  disjoint Y u
  disjoint Y v
  disjoint ph u
  disjoint ph v
  assert |- ( ph -> ( F e. ( U uCn V ) <-> ( F : X --> Y /\ A. s e. S E. r e. R A. x e. X A. y e. X ( x r y -> ( F ` x ) s ( F ` y ) ) ) ) )

  proof
    wph
    cF
    cU
    cV
    cucn
    co
    wcel
    #
    cX
    cY
    cF
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    vu
    cv
    #
    wbr
    #
    @2
    cF
    cfv
    #
    @3
    cF
    cfv
    #
    vv
    cv
    #
    wbr
    #
    wi
    #
    vy
    cX
    wral
    #
    vx
    cX
    wral
    #
    vu
    cU
    wrex
    #
    vv
    cV
    wral
    #
    wa
    #
    @1
    @2
    @3
    vr
    cv
    #
    wbr
    #
    @6
    @7
    vs
    cv
    #
    wbr
    #
    wi
    #
    vy
    cX
    wral
    #
    vx
    cX
    wral
    #
    vr
    cR
    wrex
    #
    vs
    cS
    wral
    #
    wa
    wph
    cU
    cX
    cust
    cfv
    wcel
    cV
    cY
    cust
    cfv
    wcel
    @0
    @15
    wb
    isucn2.1
    isucn2.2
    vx
    vy
    cU
    cF
    cV
    cX
    cY
    vv
    vu
    isucn
    syl2anc
    wph
    @1
    @14
    @24
    wph
    @1
    wa
    #
    @14
    @24
    @25
    @14
    wa
    #
    @23
    vs
    cS
    @26
    @18
    cS
    wcel
    #
    wa
    #
    @5
    @19
    wi
    #
    vy
    cX
    wral
    #
    vx
    cX
    wral
    #
    vu
    cU
    wrex
    #
    @23
    @28
    @18
    cV
    wcel
    @14
    @32
    @26
    cS
    cV
    @18
    @25
    cS
    cV
    wss
    #
    @14
    wph
    @33
    @1
    wph
    cS
    cY
    cY
    cxp
    #
    cS
    cfg
    co
    #
    cV
    wph
    cS
    @34
    cfbas
    cfv
    wcel
    #
    cS
    @35
    wss
    isucn2.4
    cS
    @34
    ssfg
    syl
    isucn2.v
    syl6sseqr
    adantr
    adantr
    sselda
    @25
    @14
    @27
    simplr
    @13
    @32
    vv
    @18
    cV
    @8
    @18
    wceq
    #
    @11
    @30
    vu
    vx
    cU
    cX
    @37
    @10
    @29
    vy
    cX
    @37
    @9
    @19
    @5
    @6
    @7
    @8
    @18
    breq
    imbi2d
    ralbidv
    rexralbidv
    rspcva
    syl2anc
    wph
    @32
    @23
    wi
    @1
    @14
    @27
    wph
    @31
    @23
    vu
    cU
    wph
    @4
    cU
    wcel
    #
    wa
    #
    @31
    @22
    wi
    #
    vr
    cR
    wrex
    #
    @31
    @23
    wi
    @39
    @16
    @4
    wss
    #
    vr
    cR
    wrex
    #
    @41
    wph
    @38
    @4
    cX
    cX
    cxp
    #
    cR
    cfg
    co
    #
    wcel
    #
    @43
    @39
    @4
    cU
    @45
    wph
    @38
    simpr
    isucn2.u
    syl6eleq
    wph
    @46
    @4
    @44
    wss
    #
    @43
    wph
    cR
    @44
    cfbas
    cfv
    wcel
    #
    @46
    @47
    @43
    wa
    wb
    isucn2.3
    vr
    @4
    cR
    @44
    elfg
    syl
    simplbda
    syldan
    wph
    @43
    @41
    wi
    @38
    wph
    @42
    @40
    vr
    cR
    wph
    @16
    cR
    wcel
    wa
    #
    @42
    @40
    @49
    @42
    wa
    #
    @29
    @20
    wi
    #
    vy
    cX
    wral
    #
    vx
    cX
    wral
    @30
    @21
    wi
    #
    vx
    cX
    wral
    @40
    @50
    @52
    vx
    cX
    @50
    @51
    vy
    cX
    @42
    @51
    @49
    @42
    @17
    @5
    @19
    @16
    @4
    @2
    @3
    ssbr
    imim1d
    adantl
    ralrimivw
    ralrimivw
    @52
    @53
    vx
    cX
    @29
    @20
    vy
    cX
    ralim
    ralimi
    @30
    @21
    vx
    cX
    ralim
    3syl
    ex
    reximdva
    adantr
    mpd
    @31
    @22
    vr
    cR
    r19.37v
    syl
    rexlimdva
    ad3antrrr
    mpd
    ralrimiva
    @25
    @24
    @14
    @25
    @24
    @32
    vs
    cS
    wral
    #
    @14
    wph
    @24
    @54
    wi
    @1
    wph
    @23
    @32
    vs
    cS
    wph
    cR
    cU
    wss
    #
    @23
    @32
    wi
    wph
    cR
    @45
    cU
    wph
    @48
    cR
    @45
    wss
    isucn2.3
    cR
    @44
    ssfg
    syl
    isucn2.u
    syl6sseqr
    @55
    @23
    @22
    vr
    cU
    wrex
    @32
    @22
    vr
    cR
    cU
    ssrexv
    @22
    @31
    vr
    vu
    cU
    @16
    @4
    wceq
    #
    @20
    @29
    vx
    vy
    cX
    cX
    @56
    @17
    @5
    @19
    @2
    @3
    @16
    @4
    breq
    imbi1d
    2ralbidv
    cbvrexv
    syl6ib
    syl
    ralimdv
    adantr
    @25
    @54
    @14
    @25
    @54
    wa
    #
    @13
    vv
    cV
    @57
    @8
    cV
    wcel
    #
    wa
    #
    @18
    @8
    wss
    #
    @13
    vs
    cS
    @57
    @58
    vs
    @25
    @54
    vs
    @25
    vs
    nfv
    @32
    vs
    cS
    nfra1
    nfan
    @58
    vs
    nfv
    nfan
    @59
    @27
    wa
    #
    @60
    wa
    #
    @32
    @13
    @62
    @54
    @27
    @32
    @25
    @54
    @58
    @27
    @60
    simp-4r
    @59
    @27
    @60
    simplr
    #
    @32
    vs
    cS
    rspa
    syl2anc
    @62
    @25
    @27
    @60
    @32
    @13
    wi
    @25
    @54
    @58
    @27
    @60
    simp-4l
    @63
    @61
    @60
    simpr
    @25
    @27
    wa
    #
    @60
    wa
    #
    @31
    @12
    vu
    cU
    @65
    @30
    @11
    vx
    cX
    @65
    @29
    @10
    vy
    cX
    @65
    @19
    @9
    @5
    @60
    @19
    @9
    wi
    @64
    @18
    @8
    @6
    @7
    ssbr
    adantl
    imim2d
    ralimdv
    ralimdv
    reximdv
    syl21anc
    mpd
    @59
    @36
    @8
    @35
    wcel
    #
    @60
    vs
    cS
    wrex
    #
    wph
    @36
    @1
    @54
    @58
    isucn2.4
    ad3antrrr
    @59
    @8
    cV
    @35
    @57
    @58
    simpr
    isucn2.v
    syl6eleq
    @36
    @66
    @8
    @34
    wss
    @67
    vs
    @8
    cS
    @34
    elfg
    simplbda
    syl2anc
    r19.29af
    ralrimiva
    ex
    syld
    imp
    impbida
    pm5.32da
    bitrd
end
