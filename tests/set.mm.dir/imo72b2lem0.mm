include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cabs.mm"
include "cr.mm"
include "cima.mm"
include "clt.mm"
include "csup.mm"
include "c2.mm"
include "cc.mm"
include "wcel.mm"
include "wi.mm"
include "ffvelrnd.mm"
include "recnd.mm"
include "idi.mm"
include "mulcld.mm"
include "abscld.mm"
include "ccom.mm"
include "imaco.mm"
include "eqcomi.mm"
include "crn.mm"
include "wss.mm"
include "imassrn.mm"
include "a1i.mm"
include "wf.mm"
include "absf.mm"
include "ax-resscn.mm"
include "fssresd.mm"
include "fco2d.mm"
include "frn.mm"
include "syl.mm"
include "sstrd.mm"
include "syl5eqss.mm"
include "c0.mm"
include "wne.mm"
include "cc0.mm"
include "0re.mm"
include "ne0ii.mm"
include "wnefimgd.mm"
include "necomd.mm"
include "wceq.mm"
include "neeqtrrd.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "c1.mm"
include "1red.mm"
include "wa.mm"
include "simpr.mm"
include "breq2d.mm"
include "ralbidv.mm"
include "extoimad.mm"
include "rspcedvd.mm"
include "suprcld.mm"
include "2re.mm"
include "caddc.mm"
include "cmin.mm"
include "fveq2d.mm"
include "2cnd.mm"
include "eqeltrd.mm"
include "readdcld.mm"
include "resubcld.mm"
include "remulcld.mm"
include "abstrid.mm"
include "fvco3d.mm"
include "wfximgfd.mm"
include "eleqtrrd.mm"
include "eqeltrrd.mm"
include "suprubd.mm"
include "le2addd.mm"
include "2timesd.mm"
include "eqcomd.mm"
include "leeq2d.mm"
include "letrd.mm"
include "leeq1d.mm"
include "0le2.mm"
include "absmulrposd.mm"
include "2pos.mm"
include "wwlemuld.mm"
include "absmuld.mm"

theorem imo72b2lem0
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let vc: setvar c
  let vx: setvar x
  assume imo72b2lem0.1: |- ( ph -> F : RR --> RR )
  assume imo72b2lem0.2: |- ( ph -> G : RR --> RR )
  assume imo72b2lem0.3: |- ( ph -> A e. RR )
  assume imo72b2lem0.4: |- ( ph -> B e. RR )
  assume imo72b2lem0.5: |- ( ph -> ( ( F ` ( A + B ) ) + ( F ` ( A - B ) ) ) = ( 2 x. ( ( F ` A ) x. ( G ` B ) ) ) )
  assume imo72b2lem0.6: |- ( ph -> A. y e. RR ( abs ` ( F ` y ) ) <_ 1 )

  disjoint F y
  disjoint ph y
  disjoint F c
  disjoint F x
  disjoint c x
  disjoint x y
  disjoint c ph
  disjoint ph x
  assert |- ( ph -> ( ( abs ` ( F ` A ) ) x. ( abs ` ( G ` B ) ) ) <_ sup ( ( abs " ( F " RR ) ) , RR , < ) )

  proof
    wph
    cA
    cF
    cfv
    #
    cB
    cG
    cfv
    #
    cmul
    co
    #
    cabs
    cfv
    #
    @0
    cabs
    cfv
    @1
    cabs
    cfv
    cmul
    co
    #
    cabs
    cF
    cr
    cima
    cima
    #
    cr
    clt
    csup
    #
    wph
    @3
    @6
    c2
    wph
    @2
    wph
    @0
    @1
    wph
    @0
    cc
    wcel
    wi
    wph
    @0
    wph
    cr
    cr
    cA
    cF
    imo72b2lem0.1
    imo72b2lem0.3
    ffvelrnd
    #
    recnd
    #
    idi
    wph
    @1
    cc
    wcel
    wi
    wph
    @1
    wph
    cr
    cr
    cB
    cG
    imo72b2lem0.2
    imo72b2lem0.4
    ffvelrnd
    #
    recnd
    #
    idi
    mulcld
    #
    abscld
    #
    wph
    vc
    vx
    @5
    wph
    @5
    cabs
    cF
    ccom
    #
    cr
    cima
    #
    cr
    @14
    @5
    cabs
    cF
    cr
    imaco
    eqcomi
    #
    wph
    @14
    @13
    crn
    #
    cr
    @14
    @16
    wss
    wph
    @13
    cr
    imassrn
    a1i
    wph
    cr
    cr
    @13
    wf
    @16
    cr
    wss
    wph
    cr
    cr
    cr
    cabs
    cF
    imo72b2lem0.1
    wph
    cc
    cr
    cr
    cabs
    cc
    cr
    cabs
    wf
    wph
    absf
    a1i
    cr
    cc
    wss
    wph
    ax-resscn
    a1i
    fssresd
    fco2d
    #
    cr
    cr
    @13
    frn
    syl
    sstrd
    syl5eqss
    #
    wph
    c0
    @5
    wph
    c0
    @14
    @5
    wph
    @14
    c0
    wph
    cr
    cr
    @13
    cr
    c0
    wne
    wph
    cc0
    cr
    0re
    ne0ii
    a1i
    @17
    wnefimgd
    necomd
    @5
    @14
    wceq
    #
    wph
    @15
    a1i
    #
    neeqtrrd
    necomd
    #
    wph
    vx
    cv
    #
    vc
    cv
    #
    cle
    wbr
    #
    vx
    @5
    wral
    @22
    c1
    cle
    wbr
    #
    vx
    @5
    wral
    vc
    c1
    cr
    wph
    1red
    wph
    @23
    c1
    wceq
    #
    wa
    #
    @24
    @25
    vx
    @5
    @27
    @23
    c1
    @22
    cle
    wph
    @26
    simpr
    breq2d
    ralbidv
    wph
    vx
    vy
    c1
    cF
    imo72b2lem0.1
    imo72b2lem0.6
    extoimad
    rspcedvd
    #
    suprcld
    #
    c2
    cr
    wcel
    wph
    2re
    a1i
    #
    wph
    c2
    @2
    cmul
    co
    #
    cabs
    cfv
    #
    c2
    @3
    cmul
    co
    c2
    @6
    cmul
    co
    #
    wph
    cA
    cB
    caddc
    co
    #
    cF
    cfv
    #
    cA
    cB
    cmin
    co
    #
    cF
    cfv
    #
    caddc
    co
    #
    cabs
    cfv
    #
    @32
    @33
    wph
    @39
    @35
    cabs
    cfv
    #
    @37
    cabs
    cfv
    #
    caddc
    co
    #
    @33
    wph
    @39
    @32
    cr
    wph
    @38
    @31
    cabs
    wph
    @38
    @31
    wceq
    wi
    imo72b2lem0.5
    idi
    fveq2d
    #
    wph
    @31
    wph
    c2
    @2
    wph
    2cnd
    @11
    mulcld
    abscld
    #
    eqeltrd
    #
    wph
    @40
    @41
    wph
    @35
    wph
    @35
    wph
    cr
    cr
    @34
    cF
    wph
    cr
    cr
    cF
    wf
    wi
    imo72b2lem0.1
    idi
    #
    wph
    cA
    cB
    wph
    cA
    cr
    wcel
    wi
    imo72b2lem0.3
    idi
    #
    wph
    cB
    cr
    wcel
    wi
    imo72b2lem0.4
    idi
    #
    readdcld
    #
    ffvelrnd
    recnd
    #
    abscld
    #
    wph
    @37
    wph
    @37
    wph
    cr
    cr
    @36
    cF
    @46
    wph
    cA
    cB
    @47
    @48
    resubcld
    #
    ffvelrnd
    recnd
    #
    abscld
    #
    readdcld
    #
    wph
    c2
    @6
    @30
    @29
    remulcld
    #
    wph
    @35
    @37
    @50
    @53
    abstrid
    wph
    @42
    @6
    @6
    caddc
    co
    #
    @33
    wph
    @40
    @41
    @6
    @6
    @51
    @54
    @29
    @29
    wph
    vc
    vx
    @5
    @40
    @18
    @21
    @28
    wph
    @34
    @13
    cfv
    #
    @40
    @5
    wph
    cr
    cr
    @34
    cabs
    cF
    imo72b2lem0.1
    @49
    fvco3d
    wph
    @58
    @14
    @5
    wph
    cr
    cr
    @34
    @13
    @49
    @17
    wfximgfd
    wph
    @19
    wi
    @20
    idi
    eleqtrrd
    eqeltrrd
    suprubd
    wph
    vc
    vx
    @5
    @41
    @18
    @21
    @28
    wph
    @36
    @13
    cfv
    #
    @41
    @5
    wph
    cr
    cr
    @36
    cabs
    cF
    imo72b2lem0.1
    @52
    fvco3d
    wph
    @59
    @14
    @5
    wph
    cr
    cr
    @36
    @13
    @52
    @17
    wfximgfd
    @20
    eleqtrrd
    eqeltrrd
    suprubd
    le2addd
    wph
    @33
    @57
    wph
    @6
    wph
    @6
    @29
    recnd
    2timesd
    eqcomd
    #
    @55
    wph
    @57
    @33
    cr
    @60
    @56
    eqeltrd
    leeq2d
    letrd
    @43
    @45
    @56
    leeq1d
    wph
    c2
    @2
    cc0
    c2
    cle
    wbr
    wph
    0le2
    a1i
    @30
    wph
    @0
    @1
    wph
    @0
    cr
    wcel
    wi
    @7
    idi
    wph
    @1
    cr
    wcel
    wi
    @9
    idi
    remulcld
    absmulrposd
    @44
    @56
    leeq1d
    cc0
    c2
    clt
    wbr
    wph
    2pos
    a1i
    wwlemuld
    wph
    @3
    @4
    wceq
    wi
    wph
    @0
    @1
    @8
    @10
    absmuld
    idi
    @12
    @29
    leeq1d
end
