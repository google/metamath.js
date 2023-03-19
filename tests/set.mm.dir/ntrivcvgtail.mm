include "wceq.mm"
include "cmul.mm"
include "cseq.mm"
include "cli.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "wbr.mm"
include "wa.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cuz.mm"
include "wcel.mm"
include "wfun.mm"
include "cdm.mm"
include "cc.mm"
include "wf.mm"
include "fclim.mm"
include "ffun.mm"
include "ax-mp.mm"
include "funbrfv.mm"
include "mpsyl.mm"
include "eqnetrd.mm"
include "breqtrrd.mm"
include "jca.mm"
include "adantr.mm"
include "wb.mm"
include "seqeq1.mm"
include "fveq2d.mm"
include "neeq1d.mm"
include "breq12d.mm"
include "anbi12d.mm"
include "adantl.mm"
include "mpbird.mm"
include "caddc.mm"
include "cdiv.mm"
include "simpr.mm"
include "syl6eleqr.mm"
include "cv.mm"
include "adantlr.mm"
include "ntrivcvgfvn0.mm"
include "clim2div.mm"
include "climcl.mm"
include "syl.mm"
include "cz.mm"
include "eluzel2.mm"
include "eleq2s.mm"
include "prodf.mm"
include "feq2i.mm"
include "sylib.mm"
include "ffvelrnda.mm"
include "divne0d.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "sseldi.mm"
include "zcnd.mm"
include "1cnd.mm"
include "npcand.mm"
include "seqeq1d.mm"
include "mpbi2and.mm"
include "wo.mm"
include "syl6eleq.mm"
include "uzm1.mm"
include "mpjaodan.mm"

theorem ntrivcvgtail
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let cX: class X
  let cZ: class Z
  assume ntrivcvgtail.1: |- Z = ( ZZ>= ` M )
  assume ntrivcvgtail.2: |- ( ph -> N e. Z )
  assume ntrivcvgtail.3: |- ( ph -> seq M ( x. , F ) ~~> X )
  assume ntrivcvgtail.4: |- ( ph -> X =/= 0 )
  assume ntrivcvgtail.5: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC )

  disjoint F k
  disjoint k ph
  disjoint M k
  disjoint N k
  disjoint Z k
  assert |- ( ph -> ( ( ~~> ` seq N ( x. , F ) ) =/= 0 /\ seq N ( x. , F ) ~~> ( ~~> ` seq N ( x. , F ) ) ) )

  proof
    wph
    cN
    cM
    wceq
    #
    cmul
    cF
    cN
    cseq
    #
    cli
    cfv
    #
    cc0
    wne
    #
    @1
    @2
    cli
    wbr
    #
    wa
    #
    cN
    c1
    cmin
    co
    #
    cM
    cuz
    cfv
    #
    wcel
    #
    wph
    @0
    wa
    @5
    cmul
    cF
    cM
    cseq
    #
    cli
    cfv
    #
    cc0
    wne
    #
    @9
    @10
    cli
    wbr
    #
    wa
    #
    wph
    @13
    @0
    wph
    @11
    @12
    wph
    @10
    cX
    cc0
    cli
    wfun
    #
    wph
    @9
    cX
    cli
    wbr
    #
    @10
    cX
    wceq
    cli
    cdm
    #
    cc
    cli
    wf
    @14
    fclim
    @16
    cc
    cli
    ffun
    ax-mp
    #
    ntrivcvgtail.3
    @9
    cX
    cli
    funbrfv
    mpsyl
    #
    ntrivcvgtail.4
    eqnetrd
    wph
    @9
    cX
    @10
    cli
    ntrivcvgtail.3
    @18
    breqtrrd
    jca
    adantr
    @0
    @5
    @13
    wb
    wph
    @0
    @3
    @11
    @4
    @12
    @0
    @2
    @10
    cc0
    @0
    @1
    @9
    cli
    cmul
    cF
    cN
    cM
    seqeq1
    #
    fveq2d
    #
    neeq1d
    @0
    @1
    @9
    @2
    @10
    cli
    @19
    @20
    breq12d
    anbi12d
    adantl
    mpbird
    wph
    @8
    wa
    #
    cmul
    cF
    @6
    c1
    caddc
    co
    #
    cseq
    #
    cli
    cfv
    #
    cc0
    wne
    #
    @23
    @24
    cli
    wbr
    #
    @5
    @21
    @24
    cX
    @6
    @9
    cfv
    #
    cdiv
    co
    #
    cc0
    @14
    @21
    @23
    @28
    cli
    wbr
    @24
    @28
    wceq
    @17
    @21
    cX
    vk
    cF
    cM
    @6
    cZ
    ntrivcvgtail.1
    @21
    @6
    @7
    cZ
    wph
    @8
    simpr
    ntrivcvgtail.1
    syl6eleqr
    #
    wph
    vk
    cv
    #
    cZ
    wcel
    @30
    cF
    cfv
    cc
    wcel
    @8
    ntrivcvgtail.5
    adantlr
    #
    wph
    @15
    @8
    ntrivcvgtail.3
    adantr
    #
    @21
    vk
    cF
    cM
    @6
    cX
    cZ
    ntrivcvgtail.1
    @29
    @32
    wph
    cX
    cc0
    wne
    @8
    ntrivcvgtail.4
    adantr
    #
    @31
    ntrivcvgfvn0
    #
    clim2div
    #
    @23
    @28
    cli
    funbrfv
    mpsyl
    #
    @21
    cX
    @27
    wph
    cX
    cc
    wcel
    #
    @8
    wph
    @15
    @37
    ntrivcvgtail.3
    cX
    @9
    climcl
    syl
    adantr
    wph
    @7
    cc
    @6
    @9
    wph
    cZ
    cc
    @9
    wf
    @7
    cc
    @9
    wf
    wph
    vk
    cF
    cM
    cZ
    ntrivcvgtail.1
    wph
    cN
    cZ
    wcel
    cM
    cz
    wcel
    #
    ntrivcvgtail.2
    @38
    cN
    @7
    cZ
    cM
    cN
    eluzel2
    ntrivcvgtail.1
    eleq2s
    syl
    ntrivcvgtail.5
    prodf
    cZ
    @7
    cc
    @9
    ntrivcvgtail.1
    feq2i
    sylib
    ffvelrnda
    @33
    @34
    divne0d
    eqnetrd
    @21
    @23
    @28
    @24
    cli
    @35
    @36
    breqtrrd
    @21
    @25
    @3
    @26
    @4
    @21
    @24
    @2
    cc0
    @21
    @23
    @1
    cli
    @21
    @22
    cN
    cmul
    cF
    @21
    cN
    c1
    wph
    cN
    cc
    wcel
    @8
    wph
    cN
    wph
    cZ
    cz
    cN
    cZ
    @7
    cz
    ntrivcvgtail.1
    cM
    uzssz
    eqsstri
    ntrivcvgtail.2
    sseldi
    zcnd
    adantr
    @21
    1cnd
    npcand
    seqeq1d
    #
    fveq2d
    #
    neeq1d
    @21
    @23
    @1
    @24
    @2
    cli
    @39
    @40
    breq12d
    anbi12d
    mpbi2and
    wph
    cN
    @7
    wcel
    @0
    @8
    wo
    wph
    cN
    cZ
    @7
    ntrivcvgtail.2
    ntrivcvgtail.1
    syl6eleq
    cM
    cN
    uzm1
    syl
    mpjaodan
end
