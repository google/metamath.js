include "cc.mm"
include "wcel.mm"
include "csin.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "crab.mm"
include "ccot.mm"
include "ccos.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "elrab.mm"
include "oveq12d.mm"
include "df-cot.mm"
include "ovex.mm"
include "fvmpt.mm"
include "sylbir.mm"

theorem cotval
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k


  assert |- ( ( A e. CC /\ ( sin ` A ) =/= 0 ) -> ( cot ` A ) = ( ( cos ` A ) / ( sin ` A ) ) )

  proof
    cA
    cc
    wcel
    cA
    csin
    cfv
    #
    cc0
    wne
    #
    wa
    cA
    vy
    cv
    #
    csin
    cfv
    #
    cc0
    wne
    #
    vy
    cc
    crab
    #
    wcel
    cA
    ccot
    cfv
    cA
    ccos
    cfv
    #
    @0
    cdiv
    co
    #
    wceq
    @4
    @1
    vy
    cA
    cc
    @2
    cA
    wceq
    @3
    @0
    cc0
    @2
    cA
    csin
    fveq2
    neeq1d
    elrab
    vx
    cA
    vx
    cv
    #
    ccos
    cfv
    #
    @8
    csin
    cfv
    #
    cdiv
    co
    @7
    @5
    ccot
    @8
    cA
    wceq
    @9
    @6
    @10
    @0
    cdiv
    @8
    cA
    ccos
    fveq2
    @8
    cA
    csin
    fveq2
    oveq12d
    vx
    vy
    df-cot
    @6
    @0
    cdiv
    ovex
    fvmpt
    sylbir
end
