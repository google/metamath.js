include "wal.mm"
include "wsbc.mm"
include "cvv.mm"
include "wcel.mm"
include "sbcex.mm"
include "sps.mm"
include "wsb.mm"
include "dfsbcq2.mm"
include "cv.mm"
include "wceq.mm"
include "albidv.mm"
include "sbal.mm"
include "vtoclbg.mm"
include "pm5.21nii.mm"

theorem sbcal
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
  assert |- ( [. A / y ]. A. x ph <-> A. x [. A / y ]. ph )

  proof
    wph
    vx
    wal
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
    wal
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
    sps
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
    wal
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
    albidv
    wph
    vx
    vy
    vz
    sbal
    vtoclbg
    pm5.21nii
end
