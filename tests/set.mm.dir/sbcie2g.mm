include "cv.mm"
include "wsbc.mm"
include "dfsbcq.mm"
include "wsb.mm"
include "sbsbc.mm"
include "nfv.mm"
include "sbie.mm"
include "bitr3i.mm"
include "vtoclbg.mm"

theorem sbcie2g
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cV: class V
  assume sbcie2g.1: |- ( x = y -> ( ph <-> ps ) )
  assume sbcie2g.2: |- ( y = A -> ( ps <-> ch ) )

  disjoint x y
  disjoint A y
  disjoint ch y
  disjoint ph y
  disjoint ps x
  assert |- ( A e. V -> ( [. A / x ]. ph <-> ch ) )

  proof
    wph
    vx
    vy
    cv
    #
    wsbc
    #
    wps
    wph
    vx
    cA
    wsbc
    wch
    vy
    cA
    cV
    wph
    vx
    @0
    cA
    dfsbcq
    sbcie2g.2
    @1
    wph
    vx
    vy
    wsb
    wps
    wph
    vx
    vy
    sbsbc
    wph
    wps
    vx
    vy
    wps
    vx
    nfv
    sbcie2g.1
    sbie
    bitr3i
    vtoclbg
end
