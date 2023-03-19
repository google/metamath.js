include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "csb.mm"
include "wsbc.mm"
include "sbcan.mm"
include "sbc5.mm"
include "csbconstgi.mm"
include "eqid.mm"
include "sbceqi.mm"
include "anbi1i.mm"
include "3bitr3i.mm"
include "exbii.mm"
include "sbcbii.mm"
include "bitri.mm"
include "19.42v.mm"
include "bicomi.mm"
include "excom.mm"
include "3bitr4i.mm"

theorem sbccom2lem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume sbccom2lem.1: |- A e. _V

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  assert |- ( [. A / x ]. [. B / y ]. ph <-> [. [_ A / x ]_ B / y ]. [. A / x ]. ph )

  proof
    vx
    cv
    cA
    wceq
    #
    vy
    cv
    #
    cB
    wceq
    #
    wph
    wa
    #
    wa
    #
    vx
    wex
    #
    vy
    wex
    #
    @1
    vx
    cA
    cB
    csb
    #
    wceq
    #
    wph
    vx
    cA
    wsbc
    #
    wa
    #
    vy
    wex
    wph
    vy
    cB
    wsbc
    #
    vx
    cA
    wsbc
    #
    @9
    vy
    @7
    wsbc
    @5
    @10
    vy
    @3
    vx
    cA
    wsbc
    @2
    vx
    cA
    wsbc
    #
    @9
    wa
    @5
    @10
    @2
    wph
    vx
    cA
    sbcan
    @3
    vx
    cA
    sbc5
    @13
    @8
    @9
    vx
    cA
    @1
    cB
    @1
    @7
    sbccom2lem.1
    vx
    vy
    cA
    sbccom2lem.1
    csbconstgi
    @7
    eqid
    sbceqi
    anbi1i
    3bitr3i
    exbii
    @12
    @0
    @3
    vy
    wex
    #
    wa
    #
    vx
    wex
    #
    @6
    @12
    @14
    vx
    cA
    wsbc
    @16
    @11
    @14
    vx
    cA
    wph
    vy
    cB
    sbc5
    sbcbii
    @14
    vx
    cA
    sbc5
    bitri
    @16
    @4
    vy
    wex
    #
    vx
    wex
    @6
    @15
    @17
    vx
    @17
    @15
    @0
    @3
    vy
    19.42v
    bicomi
    exbii
    @4
    vx
    vy
    excom
    bitri
    bitri
    @9
    vy
    @7
    sbc5
    3bitr4i
end
