include "crn.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cxr.mm"
include "cli.mm"
include "climinf.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wceq.mm"
include "frnd.mm"
include "cfv.mm"
include "wfn.mm"
include "wcel.mm"
include "ffnd.mm"
include "uzidd2.mm"
include "fnfvelrn.mm"
include "syl2anc.mm"
include "ne0d.mm"
include "wa.mm"
include "simpr.mm"
include "wb.mm"
include "fvelrnb.mm"
include "syl.mm"
include "adantr.mm"
include "mpbid.mm"
include "adantlr.mm"
include "wi.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "rspa.mm"
include "simpl.mm"
include "breqtrd.mm"
include "ex.mm"
include "adantl.mm"
include "rexlimd.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "reximdva.mm"
include "infxrre.mm"
include "syl3anc.mm"
include "breqtrrd.mm"

theorem climinf2lem
  let wph: wff ph
  let vx: setvar x
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vy: setvar y
  assume climinf2lem.1: |- Z = ( ZZ>= ` M )
  assume climinf2lem.2: |- ( ph -> M e. ZZ )
  assume climinf2lem.3: |- ( ph -> F : Z --> RR )
  assume climinf2lem.4: |- ( ( ph /\ k e. Z ) -> ( F ` ( k + 1 ) ) <_ ( F ` k ) )
  assume climinf2lem.5: |- ( ph -> E. x e. RR A. k e. Z x <_ ( F ` k ) )

  disjoint F k
  disjoint F x
  disjoint k x
  disjoint Z k
  disjoint Z x
  disjoint k ph
  disjoint ph x
  disjoint F y
  disjoint k y
  disjoint x y
  disjoint Z y
  disjoint ph y
  assert |- ( ph -> F ~~> inf ( ran F , RR* , < ) )

  proof
    wph
    cF
    cF
    crn
    #
    cr
    clt
    cinf
    #
    @0
    cxr
    clt
    cinf
    #
    cli
    wph
    vx
    vk
    cF
    cM
    cZ
    climinf2lem.1
    climinf2lem.2
    climinf2lem.3
    climinf2lem.4
    climinf2lem.5
    climinf
    wph
    @0
    cr
    wss
    @0
    c0
    wne
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vy
    @0
    wral
    #
    vx
    cr
    wrex
    #
    @2
    @1
    wceq
    wph
    cZ
    cr
    cF
    climinf2lem.3
    frnd
    wph
    @0
    cM
    cF
    cfv
    #
    wph
    cF
    cZ
    wfn
    #
    cM
    cZ
    wcel
    @8
    @0
    wcel
    wph
    cZ
    cr
    cF
    climinf2lem.3
    ffnd
    #
    wph
    cM
    cZ
    climinf2lem.2
    climinf2lem.1
    uzidd2
    cZ
    cM
    cF
    fnfvelrn
    syl2anc
    ne0d
    wph
    @3
    vk
    cv
    #
    cF
    cfv
    #
    cle
    wbr
    #
    vk
    cZ
    wral
    #
    vx
    cr
    wrex
    @7
    climinf2lem.5
    wph
    @14
    @6
    vx
    cr
    wph
    @3
    cr
    wcel
    #
    wa
    @14
    @6
    wph
    @14
    @6
    @15
    wph
    @14
    wa
    #
    @5
    vy
    @0
    @16
    @4
    @0
    wcel
    #
    wa
    @12
    @4
    wceq
    #
    vk
    cZ
    wrex
    #
    @5
    wph
    @17
    @19
    @14
    wph
    @17
    wa
    @17
    @19
    wph
    @17
    simpr
    wph
    @17
    @19
    wb
    #
    @17
    wph
    @9
    @20
    @10
    vk
    cZ
    @4
    cF
    fvelrnb
    syl
    adantr
    mpbid
    adantlr
    @16
    @19
    @5
    wi
    @17
    @16
    @18
    @5
    vk
    cZ
    wph
    @14
    vk
    wph
    vk
    nfv
    @13
    vk
    cZ
    nfra1
    nfan
    @5
    vk
    nfv
    @14
    @11
    cZ
    wcel
    #
    @18
    @5
    wi
    #
    wi
    wph
    @14
    @21
    @22
    @14
    @21
    wa
    @13
    @22
    @13
    vk
    cZ
    rspa
    @13
    @18
    @5
    @13
    @18
    wa
    @3
    @12
    @4
    cle
    @13
    @18
    simpl
    @13
    @18
    simpr
    breqtrd
    ex
    syl
    ex
    adantl
    rexlimd
    adantr
    mpd
    ralrimiva
    adantlr
    ex
    reximdva
    mpd
    vx
    vy
    @0
    infxrre
    syl3anc
    breqtrrd
end
