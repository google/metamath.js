include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "copab.mm"
include "3anass.mm"
include "opabbii.mm"
include "syl6eq.mm"
include "wceq.mm"
include "anbi12d.mm"
include "rbropap.mm"
include "syl6bbr.mm"

theorem 2rbropap
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let cP: class P
  let vf: setvar f
  let cF: class F
  let cM: class M
  let cW: class W
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume 2rbropap.1: |- ( ph -> M = { <. f , p >. | ( f W p /\ ps /\ ta ) } )
  assume 2rbropap.2: |- ( ( f = F /\ p = P ) -> ( ps <-> ch ) )
  assume 2rbropap.3: |- ( ( f = F /\ p = P ) -> ( ta <-> th ) )

  disjoint F f
  disjoint F p
  disjoint f p
  disjoint P f
  disjoint P p
  disjoint W f
  disjoint W p
  disjoint ch f
  disjoint ch p
  disjoint f th
  disjoint p th
  assert |- ( ( ph /\ F e. X /\ P e. Y ) -> ( F M P <-> ( F W P /\ ch /\ th ) ) )

  proof
    wph
    cF
    cX
    wcel
    cP
    cY
    wcel
    w3a
    cF
    cP
    cM
    wbr
    cF
    cP
    cW
    wbr
    #
    wch
    wth
    wa
    #
    wa
    @0
    wch
    wth
    w3a
    wph
    wps
    wta
    wa
    #
    @1
    cP
    vf
    cF
    cM
    cW
    cX
    cY
    vp
    wph
    cM
    vf
    cv
    #
    vp
    cv
    #
    cW
    wbr
    #
    wps
    wta
    w3a
    #
    vf
    vp
    copab
    @5
    @2
    wa
    #
    vf
    vp
    copab
    2rbropap.1
    @6
    @7
    vf
    vp
    @5
    wps
    wta
    3anass
    opabbii
    syl6eq
    @3
    cF
    wceq
    @4
    cP
    wceq
    wa
    wps
    wch
    wta
    wth
    2rbropap.2
    2rbropap.3
    anbi12d
    rbropap
    @0
    wch
    wth
    3anass
    syl6bbr
end
