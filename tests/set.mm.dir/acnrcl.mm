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
include "wne.mm"
include "ne0i.mm"
include "abn0.mm"
include "simpl.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "syl.mm"
include "df-acn.mm"
include "eleq2s.mm"

theorem acnrcl
  let cA: class A
  let cX: class X
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
  let cC: class C


  assert |- ( X e. AC_ A -> A e. _V )

  proof
    cA
    cvv
    wcel
    #
    cX
    @0
    vy
    cv
    #
    vg
    cv
    cfv
    @1
    vf
    cv
    cfv
    wcel
    vy
    cA
    wral
    vg
    wex
    vf
    vx
    cv
    cpw
    c0
    csn
    cdif
    cA
    cmap
    co
    wral
    #
    wa
    #
    vx
    cab
    #
    cA
    wacn
    cX
    @4
    wcel
    @4
    c0
    wne
    #
    @0
    @4
    cX
    ne0i
    @5
    @3
    vx
    wex
    @0
    @3
    vx
    abn0
    @3
    @0
    vx
    @0
    @2
    simpl
    exlimiv
    sylbi
    syl
    vx
    vy
    cA
    vf
    vg
    df-acn
    eleq2s
end
