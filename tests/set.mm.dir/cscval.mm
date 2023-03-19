include "cc.mm"
include "wcel.mm"
include "csin.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "crab.mm"
include "ccsc.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "elrab.mm"
include "oveq2d.mm"
include "df-csc.mm"
include "ovex.mm"
include "fvmpt.mm"
include "sylbir.mm"

theorem cscval
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k


  assert |- ( ( A e. CC /\ ( sin ` A ) =/= 0 ) -> ( csc ` A ) = ( 1 / ( sin ` A ) ) )

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
    ccsc
    cfv
    c1
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
    c1
    vx
    cv
    #
    csin
    cfv
    #
    cdiv
    co
    @6
    @5
    ccsc
    @7
    cA
    wceq
    @8
    @0
    c1
    cdiv
    @7
    cA
    csin
    fveq2
    oveq2d
    vx
    vy
    df-csc
    c1
    @0
    cdiv
    ovex
    fvmpt
    sylbir
end
