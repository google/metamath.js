include "wa.mm"
include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "wral.mm"
include "wrex.mm"
include "jca.mm"
include "rexanuz2.mm"
include "sylibr.mm"
include "wcel.mm"
include "wi.mm"
include "cz.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "eluzelz.mm"
include "uzid.mm"
include "3syl.mm"
include "adantr.mm"
include "simpr.mm"
include "wceq.mm"
include "anbi12d.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "adantll.mm"
include "ex.mm"
include "reximdai.mm"
include "mpd.mm"

theorem rexanuz3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cZ: class Z
  assume rexanuz3.1: |- F/ j ph
  assume rexanuz3.2: |- Z = ( ZZ>= ` M )
  assume rexanuz3.3: |- ( ph -> E. j e. Z A. k e. ( ZZ>= ` j ) ch )
  assume rexanuz3.4: |- ( ph -> E. j e. Z A. k e. ( ZZ>= ` j ) ps )
  assume rexanuz3.5: |- ( k = j -> ( ch <-> th ) )
  assume rexanuz3.6: |- ( k = j -> ( ps <-> ta ) )

  disjoint M j
  disjoint Z j
  disjoint Z k
  disjoint j k
  disjoint ch j
  disjoint j ps
  disjoint k ta
  disjoint k th
  assert |- ( ph -> E. j e. Z ( th /\ ta ) )

  proof
    wph
    wch
    wps
    wa
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cZ
    wrex
    #
    wth
    wta
    wa
    #
    vj
    cZ
    wrex
    wph
    wch
    vk
    @2
    wral
    vj
    cZ
    wrex
    #
    wps
    vk
    @2
    wral
    vj
    cZ
    wrex
    #
    wa
    @4
    wph
    @6
    @7
    rexanuz3.3
    rexanuz3.4
    jca
    wch
    wps
    vj
    vk
    cM
    cZ
    rexanuz3.2
    rexanuz2
    sylibr
    wph
    @3
    @5
    vj
    cZ
    rexanuz3.1
    wph
    @1
    cZ
    wcel
    #
    @3
    @5
    wi
    wph
    @8
    wa
    @3
    @5
    @8
    @3
    @5
    wph
    @8
    @3
    wa
    @1
    @2
    wcel
    #
    @3
    @5
    @8
    @9
    @3
    @8
    @1
    cM
    cuz
    cfv
    #
    wcel
    #
    @1
    cz
    wcel
    @9
    @8
    @11
    cZ
    @10
    @1
    rexanuz3.2
    eleq2i
    biimpi
    cM
    @1
    eluzelz
    @1
    uzid
    3syl
    adantr
    @8
    @3
    simpr
    @0
    @5
    vk
    @1
    @2
    vk
    cv
    @1
    wceq
    wch
    wth
    wps
    wta
    rexanuz3.5
    rexanuz3.6
    anbi12d
    rspcva
    syl2anc
    adantll
    ex
    ex
    reximdai
    mpd
end
