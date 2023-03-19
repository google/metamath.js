include "wsbc.mm"
include "cv.mm"
include "csb.mm"
include "sbcco.mm"
include "bicomi.mm"
include "sbcbii.mm"
include "sbccom2.mm"
include "vex.mm"
include "wceq.mm"
include "wb.mm"
include "eqidd.mm"
include "csbief.mm"
include "dfsbcq.mm"
include "ax-mp.mm"
include "bitri.mm"
include "3bitri.mm"

theorem sbccom2f
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  assume sbccom2f.1: |- A e. _V
  assume sbccom2f.2: |- F/_ y A

  disjoint x y
  disjoint ph z
  disjoint x z
  disjoint y z
  disjoint A z
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
    wph
    vy
    vz
    cv
    #
    wsbc
    #
    vz
    cB
    wsbc
    #
    vx
    cA
    wsbc
    @2
    vx
    cA
    wsbc
    #
    vz
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
    @5
    wsbc
    #
    @0
    @3
    vx
    cA
    @3
    @0
    wph
    vy
    vz
    cB
    sbcco
    bicomi
    sbcbii
    @2
    vx
    vz
    cA
    cB
    sbccom2f.1
    sbccom2
    @6
    @7
    vy
    @1
    wsbc
    #
    vz
    @5
    wsbc
    @8
    @4
    @9
    vz
    @5
    @9
    @4
    @9
    @2
    vx
    vy
    @1
    cA
    csb
    #
    wsbc
    #
    @4
    wph
    vy
    vx
    @1
    cA
    vz
    vex
    #
    sbccom2
    @10
    cA
    wceq
    @11
    @4
    wb
    vy
    @1
    cA
    cA
    @12
    sbccom2f.2
    vy
    cv
    @1
    wceq
    cA
    eqidd
    csbief
    @2
    vx
    @10
    cA
    dfsbcq
    ax-mp
    bitri
    bicomi
    sbcbii
    @7
    vy
    vz
    @5
    sbcco
    bitri
    3bitri
end
