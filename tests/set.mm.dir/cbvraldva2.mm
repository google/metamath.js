include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "weq.mm"
include "wa.mm"
include "simpr.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "cbvaldva.mm"
include "df-ral.mm"
include "3bitr4g.mm"

theorem cbvraldva2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume cbvraldva2.1: |- ( ( ph /\ x = y ) -> ( ps <-> ch ) )
  assume cbvraldva2.2: |- ( ( ph /\ x = y ) -> A = B )

  disjoint A y
  disjoint ps y
  disjoint B x
  disjoint ch x
  disjoint ph x
  disjoint x y
  disjoint ph y
  assert |- ( ph -> ( A. x e. A ps <-> A. y e. B ch ) )

  proof
    wph
    vx
    cv
    #
    cA
    wcel
    #
    wps
    wi
    #
    vx
    wal
    vy
    cv
    #
    cB
    wcel
    #
    wch
    wi
    #
    vy
    wal
    wps
    vx
    cA
    wral
    wch
    vy
    cB
    wral
    wph
    @2
    @5
    vx
    vy
    wph
    vx
    vy
    weq
    #
    wa
    #
    @1
    @4
    wps
    wch
    @7
    @0
    @3
    cA
    cB
    wph
    @6
    simpr
    cbvraldva2.2
    eleq12d
    cbvraldva2.1
    imbi12d
    cbvaldva
    wps
    vx
    cA
    df-ral
    wch
    vy
    cB
    df-ral
    3bitr4g
end
