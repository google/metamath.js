include "wcel.mm"
include "wa.mm"
include "crg.mm"
include "cin.mm"
include "cv.mm"
include "eleq1.mm"
include "vtoclri.mm"
include "anim2i.mm"
include "elin2.mm"
include "elin.mm"
include "3imtr4i.mm"

theorem srhmsubclem1
  let cC: class C
  let cS: class S
  let cU: class U
  let cX: class X
  let vr: setvar r
  let vk: setvar k
  let vx: setvar x
  assume srhmsubc.s: |- A. r e. S r e. Ring
  assume srhmsubc.c: |- C = ( U i^i S )

  disjoint S r
  disjoint X r
  disjoint k x
  assert |- ( X e. C -> X e. ( U i^i Ring ) )

  proof
    cX
    cU
    wcel
    #
    cX
    cS
    wcel
    #
    wa
    @0
    cX
    crg
    wcel
    #
    wa
    cX
    cC
    wcel
    cX
    cU
    crg
    cin
    wcel
    @1
    @2
    @0
    vr
    cv
    #
    crg
    wcel
    @2
    vr
    cX
    cS
    @3
    cX
    crg
    eleq1
    srhmsubc.s
    vtoclri
    anim2i
    cX
    cU
    cS
    cC
    srhmsubc.c
    elin2
    cX
    cU
    crg
    elin
    3imtr4i
end
