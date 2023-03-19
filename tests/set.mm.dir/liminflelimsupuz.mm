include "cvv.mm"
include "cxr.mm"
include "wcel.mm"
include "cuz.mm"
include "fvexi.mm"
include "a1i.mm"
include "fexd.mm"
include "cv.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "wrex.mm"
include "cr.mm"
include "wral.mm"
include "cima.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "uzubico2.mm"
include "wa.mm"
include "wi.mm"
include "cfv.mm"
include "wfn.mm"
include "ffnd.mm"
include "adantr.mm"
include "simpr.mm"
include "id.mm"
include "uzxrd.mm"
include "pnfxr.mm"
include "xrleidd.mm"
include "clt.mm"
include "wbr.mm"
include "uzred.mm"
include "ltpnf.mm"
include "syl.mm"
include "elicod.mm"
include "adantl.mm"
include "fnfvima2.mm"
include "ffvelrnda.mm"
include "elind.mm"
include "ne0i.mm"
include "ex.mm"
include "ad2antrr.mm"
include "reximdva.mm"
include "ralimdva.mm"
include "mpd.mm"
include "liminflelimsup.mm"

theorem liminflelimsupuz
  let wph: wff ph
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  assume liminflelimsupuz.1: |- ( ph -> M e. ZZ )
  assume liminflelimsupuz.2: |- Z = ( ZZ>= ` M )
  assume liminflelimsupuz.3: |- ( ph -> F : Z --> RR* )


  assert |- ( ph -> ( liminf ` F ) <_ ( limsup ` F ) )

  proof
    wph
    vj
    vk
    cF
    cvv
    wph
    cZ
    cxr
    cvv
    cF
    liminflelimsupuz.3
    cZ
    cvv
    wcel
    wph
    cZ
    cM
    cuz
    liminflelimsupuz.2
    fvexi
    a1i
    fexd
    wph
    vj
    cv
    #
    cZ
    wcel
    #
    vj
    vk
    cv
    #
    cpnf
    cico
    co
    #
    wrex
    #
    vk
    cr
    wral
    cF
    @0
    cpnf
    cico
    co
    #
    cima
    #
    cxr
    cin
    #
    c0
    wne
    #
    vj
    @3
    wrex
    #
    vk
    cr
    wral
    wph
    vk
    vj
    cM
    cZ
    liminflelimsupuz.1
    liminflelimsupuz.2
    uzubico2
    wph
    @4
    @9
    vk
    cr
    wph
    @2
    cr
    wcel
    #
    wa
    @1
    @8
    vj
    @3
    wph
    @1
    @8
    wi
    @10
    @0
    @3
    wcel
    wph
    @1
    @8
    wph
    @1
    wa
    #
    @0
    cF
    cfv
    #
    @7
    wcel
    @8
    @11
    @6
    cxr
    @12
    @11
    cZ
    @0
    @5
    cF
    wph
    cF
    cZ
    wfn
    @1
    wph
    cZ
    cxr
    cF
    liminflelimsupuz.3
    ffnd
    adantr
    wph
    @1
    simpr
    @1
    @0
    @5
    wcel
    wph
    @1
    @0
    cpnf
    @0
    @1
    @0
    cM
    cZ
    liminflelimsupuz.2
    @1
    id
    #
    uzxrd
    #
    cpnf
    cxr
    wcel
    @1
    pnfxr
    a1i
    @14
    @1
    @0
    @14
    xrleidd
    @1
    @0
    cr
    wcel
    @0
    cpnf
    clt
    wbr
    @1
    @0
    cM
    cZ
    liminflelimsupuz.2
    @13
    uzred
    @0
    ltpnf
    syl
    elicod
    adantl
    fnfvima2
    wph
    cZ
    cxr
    @0
    cF
    liminflelimsupuz.3
    ffvelrnda
    elind
    @7
    @12
    ne0i
    syl
    ex
    ad2antrr
    reximdva
    ralimdva
    mpd
    liminflelimsup
end
