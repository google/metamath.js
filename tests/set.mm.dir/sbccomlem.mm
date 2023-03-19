include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "wsbc.mm"
include "excom.mm"
include "exdistr.mm"
include "an12.mm"
include "exbii.mm"
include "19.42v.mm"
include "bitri.mm"
include "3bitr3i.mm"
include "sbc5.mm"
include "3bitr4i.mm"
include "sbcbii.mm"

theorem sbccomlem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  assert |- ( [. A / x ]. [. B / y ]. ph <-> [. B / y ]. [. A / x ]. ph )

  proof
    vy
    cv
    cB
    wceq
    #
    wph
    wa
    #
    vy
    wex
    #
    vx
    cA
    wsbc
    #
    vx
    cv
    cA
    wceq
    #
    wph
    wa
    #
    vx
    wex
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
    @4
    @2
    wa
    vx
    wex
    #
    @0
    @6
    wa
    #
    vy
    wex
    #
    @3
    @7
    @4
    @1
    wa
    #
    vy
    wex
    vx
    wex
    @13
    vx
    wex
    #
    vy
    wex
    @10
    @12
    @13
    vx
    vy
    excom
    @4
    @1
    vx
    vy
    exdistr
    @14
    @11
    vy
    @14
    @0
    @5
    wa
    #
    vx
    wex
    @11
    @13
    @15
    vx
    @4
    @0
    wph
    an12
    exbii
    @0
    @5
    vx
    19.42v
    bitri
    exbii
    3bitr3i
    @2
    vx
    cA
    sbc5
    @6
    vy
    cB
    sbc5
    3bitr4i
    @8
    @2
    vx
    cA
    wph
    vy
    cB
    sbc5
    sbcbii
    @9
    @6
    vy
    cB
    wph
    vx
    cA
    sbc5
    sbcbii
    3bitr4i
end
