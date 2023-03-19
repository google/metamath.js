include "wex.mm"
include "wsbc.mm"
include "sbcexf.mm"
include "exbii.mm"
include "bitri.mm"

theorem sbcexfi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume sbcexfi.1: |- F/_ y A
  assume sbcexfi.2: |- ( [. A / x ]. ph <-> ps )

  disjoint x y
  assert |- ( [. A / x ]. E. y ph <-> E. y ps )

  proof
    wph
    vy
    wex
    vx
    cA
    wsbc
    wph
    vx
    cA
    wsbc
    #
    vy
    wex
    wps
    vy
    wex
    wph
    vx
    vy
    cA
    sbcexfi.1
    sbcexf
    @0
    wps
    vy
    sbcexfi.2
    exbii
    bitri
end
