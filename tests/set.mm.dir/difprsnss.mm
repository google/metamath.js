include "cpr.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "wceq.mm"
include "wo.mm"
include "vex.mm"
include "elpr.mm"
include "velsn.mm"
include "notbii.mm"
include "biorf.mm"
include "biimparc.mm"
include "syl2anb.mm"
include "eldif.mm"
include "3imtr4i.mm"
include "ssriv.mm"

theorem difprsnss
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( { A , B } \ { A } ) C_ { B }

  proof
    vx
    cA
    cB
    cpr
    #
    cA
    csn
    #
    cdif
    #
    cB
    csn
    #
    vx
    cv
    #
    @0
    wcel
    #
    @4
    @1
    wcel
    #
    wn
    #
    wa
    @4
    cB
    wceq
    #
    @4
    @2
    wcel
    @4
    @3
    wcel
    @5
    @4
    cA
    wceq
    #
    @8
    wo
    #
    @9
    wn
    #
    @8
    @7
    @4
    cA
    cB
    vx
    vex
    elpr
    @6
    @9
    vx
    cA
    velsn
    notbii
    @11
    @8
    @10
    @9
    @8
    biorf
    biimparc
    syl2anb
    @4
    @0
    @1
    eldif
    vx
    cB
    velsn
    3imtr4i
    ssriv
end
