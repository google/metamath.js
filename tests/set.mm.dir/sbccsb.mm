include "wsbc.mm"
include "cv.mm"
include "cab.mm"
include "wcel.mm"
include "csb.mm"
include "abid.mm"
include "sbcbii.mm"
include "sbcel2.mm"
include "bitr3i.mm"

theorem sbccsb
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  assert |- ( [. A / x ]. ph <-> y e. [_ A / x ]_ { y | ph } )

  proof
    wph
    vx
    cA
    wsbc
    vy
    cv
    #
    wph
    vy
    cab
    #
    wcel
    #
    vx
    cA
    wsbc
    @0
    vx
    cA
    @1
    csb
    wcel
    @2
    wph
    vx
    cA
    wph
    vy
    abid
    sbcbii
    vx
    cA
    @0
    @1
    sbcel2
    bitr3i
end
