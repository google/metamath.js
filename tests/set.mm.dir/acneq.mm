include "wceq.mm"
include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wex.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "cmap.mm"
include "co.mm"
include "wa.mm"
include "cab.mm"
include "wacn.mm"
include "eleq1.mm"
include "oveq2.mm"
include "raleq.mm"
include "exbidv.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "abbidv.mm"
include "df-acn.mm"
include "3eqtr4g.mm"

theorem acneq
  let cA: class A
  let cC: class C
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cF: class F
  let wph: wff ph
  let wps: wff ps
  let cX: class X


  assert |- ( A = C -> AC_ A = AC_ C )

  proof
    cA
    cC
    wceq
    #
    cA
    cvv
    wcel
    #
    vy
    cv
    #
    vg
    cv
    cfv
    @2
    vf
    cv
    cfv
    wcel
    #
    vy
    cA
    wral
    #
    vg
    wex
    #
    vf
    vx
    cv
    cpw
    c0
    csn
    cdif
    #
    cA
    cmap
    co
    #
    wral
    #
    wa
    #
    vx
    cab
    cC
    cvv
    wcel
    #
    @3
    vy
    cC
    wral
    #
    vg
    wex
    #
    vf
    @6
    cC
    cmap
    co
    #
    wral
    #
    wa
    #
    vx
    cab
    cA
    wacn
    cC
    wacn
    @0
    @9
    @15
    vx
    @0
    @1
    @10
    @8
    @14
    cA
    cC
    cvv
    eleq1
    @0
    @5
    @12
    vf
    @7
    @13
    cA
    cC
    @6
    cmap
    oveq2
    @0
    @4
    @11
    vg
    @3
    vy
    cA
    cC
    raleq
    exbidv
    raleqbidv
    anbi12d
    abbidv
    vx
    vy
    cA
    vf
    vg
    df-acn
    vx
    vy
    cC
    vf
    vg
    df-acn
    3eqtr4g
end
