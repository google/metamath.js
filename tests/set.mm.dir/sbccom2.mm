include "wsbc.mm"
include "cv.mm"
include "csb.mm"
include "sbcco.mm"
include "bicomi.mm"
include "sbcbii.mm"
include "vex.mm"
include "sbccom2lem.mm"
include "3bitri.mm"
include "wceq.mm"
include "wb.mm"
include "csbco.mm"
include "dfsbcq.mm"
include "ax-mp.mm"
include "bitri.mm"
include "sbccom.mm"

theorem sbccom2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  let vw: setvar w
  assume sbccom2.1: |- A e. _V

  disjoint x y
  disjoint A y
  disjoint ph z
  disjoint ph w
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w z
  disjoint A z
  disjoint B z
  disjoint A w
  disjoint B w
  assert |- ( [. A / x ]. [. B / y ]. ph <-> [. [_ A / x ]_ B / y ]. [. A / x ]. ph )

  proof
    wph
    vy
    cB
    wsbc
    #
    vx
    cA
    wsbc
    #
    wph
    vy
    vw
    cv
    #
    wsbc
    #
    vx
    cA
    wsbc
    #
    vw
    vx
    cA
    cB
    csb
    #
    wsbc
    #
    wph
    vx
    cA
    wsbc
    #
    vy
    @2
    wsbc
    #
    vw
    @5
    wsbc
    @7
    vy
    @5
    wsbc
    @1
    @4
    vw
    vz
    cA
    vx
    vz
    cv
    #
    cB
    csb
    #
    csb
    #
    wsbc
    #
    @6
    @1
    @3
    vx
    @9
    wsbc
    #
    vw
    @10
    wsbc
    #
    vz
    cA
    wsbc
    #
    @13
    vz
    cA
    wsbc
    #
    vw
    @11
    wsbc
    @12
    @1
    @3
    vw
    cB
    wsbc
    #
    vx
    cA
    wsbc
    #
    @17
    vx
    @9
    wsbc
    #
    vz
    cA
    wsbc
    #
    @15
    @0
    @17
    vx
    cA
    @17
    @0
    wph
    vy
    vw
    cB
    sbcco
    bicomi
    sbcbii
    @20
    @18
    @17
    vx
    vz
    cA
    sbcco
    bicomi
    @19
    @14
    vz
    cA
    @3
    vx
    vw
    @9
    cB
    vz
    vex
    sbccom2lem
    sbcbii
    3bitri
    @13
    vz
    vw
    cA
    @10
    sbccom2.1
    sbccom2lem
    @16
    @4
    vw
    @11
    @3
    vx
    vz
    cA
    sbcco
    sbcbii
    3bitri
    @11
    @5
    wceq
    @12
    @6
    wb
    vx
    vz
    cA
    cB
    csbco
    @4
    vw
    @11
    @5
    dfsbcq
    ax-mp
    bitri
    @4
    @8
    vw
    @5
    wph
    vx
    vy
    cA
    @2
    sbccom
    sbcbii
    @7
    vy
    vw
    @5
    sbcco
    3bitri
end
