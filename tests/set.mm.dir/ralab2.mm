include "cab.mm"
include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "df-ral.mm"
include "nfsab1.mm"
include "nfv.mm"
include "nfim.mm"
include "weq.mm"
include "eleq1.mm"
include "abid.mm"
include "syl6bb.mm"
include "imbi12d.mm"
include "cbval.mm"
include "bitri.mm"

theorem ralab2
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
  assert |- ( A. x e. { y | ph } ps <-> A. y ( ph -> ch ) )

  proof
    wps
    vx
    wph
    vy
    cab
    #
    wral
    vx
    cv
    #
    @0
    wcel
    #
    wps
    wi
    #
    vx
    wal
    wph
    wch
    wi
    #
    vy
    wal
    wps
    vx
    @0
    df-ral
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
    nfim
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
    imbi12d
    cbval
    bitri
end
