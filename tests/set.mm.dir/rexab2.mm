include "cab.mm"
include "wrex.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "df-rex.mm"
include "nfsab1.mm"
include "nfv.mm"
include "nfan.mm"
include "weq.mm"
include "eleq1.mm"
include "abid.mm"
include "syl6bb.mm"
include "anbi12d.mm"
include "cbvex.mm"
include "bitri.mm"

theorem rexab2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume ralab2.1: |- ( x = y -> ( ps <-> ch ) )

  disjoint x y
  disjoint ch x
  disjoint ph x
  disjoint ps y
  disjoint A x
  assert |- ( E. x e. { y | ph } ps <-> E. y ( ph /\ ch ) )

  proof
    wps
    vx
    wph
    vy
    cab
    #
    wrex
    vx
    cv
    #
    @0
    wcel
    #
    wps
    wa
    #
    vx
    wex
    wph
    wch
    wa
    #
    vy
    wex
    wps
    vx
    @0
    df-rex
    @3
    @4
    vx
    vy
    @2
    wps
    vy
    wph
    vy
    vx
    nfsab1
    wps
    vy
    nfv
    nfan
    @4
    vx
    nfv
    vx
    vy
    weq
    #
    @2
    wph
    wps
    wch
    @5
    @2
    vy
    cv
    #
    @0
    wcel
    wph
    @1
    @6
    @0
    eleq1
    wph
    vy
    abid
    syl6bb
    ralab2.1
    anbi12d
    cbvex
    bitri
end
