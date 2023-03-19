include "cv.mm"
include "wsbc.mm"
include "sbccomlem.mm"
include "sbcbii.mm"
include "bitri.mm"
include "3bitr3i.mm"
include "sbcco.mm"

theorem sbccom
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vz: setvar z

  disjoint A y
  disjoint B x
  disjoint x y
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint y z
  disjoint A z
  disjoint w x
  disjoint B w
  disjoint x z
  disjoint B z
  disjoint ph w
  disjoint ph z
  assert |- ( [. A / x ]. [. B / y ]. ph <-> [. B / y ]. [. A / x ]. ph )

  proof
    wph
    vy
    vw
    cv
    #
    wsbc
    #
    vw
    cB
    wsbc
    #
    vx
    cA
    wsbc
    #
    wph
    vx
    vz
    cv
    #
    wsbc
    #
    vz
    cA
    wsbc
    #
    vy
    cB
    wsbc
    #
    wph
    vy
    cB
    wsbc
    #
    vx
    cA
    wsbc
    wph
    vx
    cA
    wsbc
    #
    vy
    cB
    wsbc
    @2
    vx
    @4
    wsbc
    #
    vz
    cA
    wsbc
    #
    @6
    vy
    @0
    wsbc
    #
    vw
    cB
    wsbc
    #
    @3
    @7
    @5
    vy
    @0
    wsbc
    #
    vw
    cB
    wsbc
    #
    vz
    cA
    wsbc
    @14
    vz
    cA
    wsbc
    #
    vw
    cB
    wsbc
    @11
    @13
    @14
    vz
    vw
    cA
    cB
    sbccomlem
    @15
    @10
    vz
    cA
    @15
    @1
    vx
    @4
    wsbc
    #
    vw
    cB
    wsbc
    @10
    @14
    @17
    vw
    cB
    wph
    vy
    vx
    @0
    @4
    sbccomlem
    sbcbii
    @1
    vw
    vx
    cB
    @4
    sbccomlem
    bitri
    sbcbii
    @16
    @12
    vw
    cB
    @5
    vz
    vy
    cA
    @0
    sbccomlem
    sbcbii
    3bitr3i
    @2
    vx
    vz
    cA
    sbcco
    @6
    vy
    vw
    cB
    sbcco
    3bitr3i
    @2
    @8
    vx
    cA
    wph
    vy
    vw
    cB
    sbcco
    sbcbii
    @6
    @9
    vy
    cB
    wph
    vx
    vz
    cA
    sbcco
    sbcbii
    3bitr3i
end
