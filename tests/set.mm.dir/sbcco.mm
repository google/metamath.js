include "cv.mm"
include "wsbc.mm"
include "cvv.mm"
include "wcel.mm"
include "sbcex.mm"
include "dfsbcq.mm"
include "wsb.mm"
include "sbsbc.mm"
include "sbbii.mm"
include "nfv.mm"
include "sbco2.mm"
include "3bitr3ri.mm"
include "bitri.mm"
include "vtoclbg.mm"
include "pm5.21nii.mm"

theorem sbcco
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z

  disjoint ph y
  disjoint x z
  disjoint A z
  disjoint y z
  disjoint ph z
  assert |- ( [. A / y ]. [. y / x ]. ph <-> [. A / x ]. ph )

  proof
    wph
    vx
    vy
    cv
    wsbc
    #
    vy
    cA
    wsbc
    #
    cA
    cvv
    wcel
    wph
    vx
    cA
    wsbc
    #
    @0
    vy
    cA
    sbcex
    wph
    vx
    cA
    sbcex
    @0
    vy
    vz
    cv
    #
    wsbc
    #
    wph
    vx
    @3
    wsbc
    #
    @1
    @2
    vz
    cA
    cvv
    @0
    vy
    @3
    cA
    dfsbcq
    wph
    vx
    @3
    cA
    dfsbcq
    @4
    wph
    vx
    vz
    wsb
    #
    @5
    wph
    vx
    vy
    wsb
    #
    vy
    vz
    wsb
    @0
    vy
    vz
    wsb
    @6
    @4
    @7
    @0
    vy
    vz
    wph
    vx
    vy
    sbsbc
    sbbii
    wph
    vx
    vz
    vy
    wph
    vy
    nfv
    sbco2
    @0
    vy
    vz
    sbsbc
    3bitr3ri
    wph
    vx
    vz
    sbsbc
    bitri
    vtoclbg
    pm5.21nii
end
