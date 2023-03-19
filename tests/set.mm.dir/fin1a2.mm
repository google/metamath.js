include "cfin1a.mm"
include "wcel.mm"
include "cv.mm"
include "cfn.mm"
include "cdif.mm"
include "cfin2.mm"
include "wo.mm"
include "cpw.mm"
include "wral.mm"
include "wss.mm"
include "elpwi.mm"
include "wa.mm"
include "fin1ai.mm"
include "fin12.mm"
include "orim2i.mm"
include "syl.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "fin1a2s.mm"
include "mpdan.mm"

theorem fin1a2
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cV: class V
  let cX: class X
  let cC: class C


  assert |- ( A e. Fin1a -> A e. Fin2 )

  proof
    cA
    cfin1a
    wcel
    #
    vb
    cv
    #
    cfn
    wcel
    #
    cA
    @1
    cdif
    #
    cfin2
    wcel
    #
    wo
    #
    vb
    cA
    cpw
    #
    wral
    cA
    cfin2
    wcel
    @0
    @5
    vb
    @6
    @1
    @6
    wcel
    @0
    @1
    cA
    wss
    #
    @5
    @1
    cA
    elpwi
    @0
    @7
    wa
    @2
    @3
    cfn
    wcel
    #
    wo
    @5
    cA
    @1
    fin1ai
    @8
    @4
    @2
    @3
    fin12
    orim2i
    syl
    sylan2
    ralrimiva
    vb
    cA
    cfin1a
    fin1a2s
    mpdan
end
