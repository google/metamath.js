include "wcel.mm"
include "wbr.mm"
include "wa.mm"
include "wb.mm"
include "rbropapd.mm"
include "3impib.mm"

theorem rbropap
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
  assert |- ( ( ph /\ F e. X /\ P e. Y ) -> ( F M P <-> ( F W P /\ ch ) ) )

  proof
    wph
    cF
    cX
    wcel
    cP
    cY
    wcel
    cF
    cP
    cM
    wbr
    cF
    cP
    cW
    wbr
    wch
    wa
    wb
    wph
    wps
    wch
    cP
    vf
    cF
    cM
    cW
    cX
    cY
    vp
    rbropapd.1
    rbropapd.2
    rbropapd
    3impib
end
