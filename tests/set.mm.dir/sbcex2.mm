include "wex.mm"
include "wsbc.mm"
include "cvv.mm"
include "wcel.mm"
include "sbcex.mm"
include "exlimiv.mm"
include "wsb.mm"
include "dfsbcq2.mm"
include "cv.mm"
include "wceq.mm"
include "exbidv.mm"
include "sbex.mm"
include "vtoclbg.mm"
include "pm5.21nii.mm"

theorem sbcex2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint A z
  disjoint y z
  disjoint ph z
  assert |- ( [. A / y ]. E. x ph <-> E. x [. A / y ]. ph )

  proof
    wph
    vx
    wex
    #
    vy
    cA
    wsbc
    #
    cA
    cvv
    wcel
    #
    wph
    vy
    cA
    wsbc
    #
    vx
    wex
    #
    @0
    vy
    cA
    sbcex
    @3
    @2
    vx
    wph
    vy
    cA
    sbcex
    exlimiv
    @0
    vy
    vz
    wsb
    wph
    vy
    vz
    wsb
    #
    vx
    wex
    @1
    @4
    vz
    cA
    cvv
    @0
    vy
    vz
    cA
    dfsbcq2
    vz
    cv
    cA
    wceq
    @5
    @3
    vx
    wph
    vy
    vz
    cA
    dfsbcq2
    exbidv
    wph
    vx
    vy
    vz
    sbex
    vtoclbg
    pm5.21nii
end
