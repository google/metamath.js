include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wb.mm"
include "cop.mm"
include "cv.mm"
include "copab.mm"
include "df-br.mm"
include "eleq2d.mm"
include "syl5bb.mm"
include "wceq.mm"
include "breq12.mm"
include "anbi12d.mm"
include "opelopabga.mm"
include "sylan9bb.mm"
include "ex.mm"

theorem rbropapd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let cP: class P
  let vf: setvar f
  let cF: class F
  let cM: class M
  let cW: class W
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume rbropapd.1: |- ( ph -> M = { <. f , p >. | ( f W p /\ ps ) } )
  assume rbropapd.2: |- ( ( f = F /\ p = P ) -> ( ps <-> ch ) )

  disjoint F f
  disjoint F p
  disjoint f p
  disjoint P f
  disjoint P p
  disjoint W f
  disjoint W p
  disjoint ch f
  disjoint ch p
  assert |- ( ph -> ( ( F e. X /\ P e. Y ) -> ( F M P <-> ( F W P /\ ch ) ) ) )

  proof
    wph
    cF
    cX
    wcel
    cP
    cY
    wcel
    wa
    #
    cF
    cP
    cM
    wbr
    #
    cF
    cP
    cW
    wbr
    #
    wch
    wa
    #
    wb
    wph
    @1
    cF
    cP
    cop
    #
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
    wa
    #
    vf
    vp
    copab
    #
    wcel
    #
    @0
    @3
    @1
    @4
    cM
    wcel
    wph
    @10
    cF
    cP
    cM
    df-br
    wph
    cM
    @9
    @4
    rbropapd.1
    eleq2d
    syl5bb
    @8
    @3
    vf
    vp
    cF
    cP
    cX
    cY
    @5
    cF
    wceq
    @6
    cP
    wceq
    wa
    @7
    @2
    wps
    wch
    @5
    cF
    @6
    cP
    cW
    breq12
    rbropapd.2
    anbi12d
    opelopabga
    sylan9bb
    ex
end
