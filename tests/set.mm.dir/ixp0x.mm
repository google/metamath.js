include "c0.mm"
include "cixp.mm"
include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "cab.mm"
include "csn.mm"
include "dfixp.mm"
include "wceq.mm"
include "velsn.mm"
include "fn0.mm"
include "ral0.mm"
include "biantru.mm"
include "3bitr2i.mm"
include "abbi2i.mm"
include "eqtr4i.mm"

theorem ixp0x
  let vx: setvar x
  let cA: class A
  let vf: setvar f


  assert |- X_ x e. (/) A = { (/) }

  proof
    vx
    c0
    cA
    cixp
    vf
    cv
    #
    c0
    wfn
    #
    vx
    cv
    @0
    cfv
    cA
    wcel
    #
    vx
    c0
    wral
    #
    wa
    #
    vf
    cab
    c0
    csn
    #
    vx
    c0
    cA
    vf
    dfixp
    @4
    vf
    @5
    @0
    @5
    wcel
    @0
    c0
    wceq
    @1
    @4
    vf
    c0
    velsn
    @0
    fn0
    @3
    @1
    @2
    vx
    ral0
    biantru
    3bitr2i
    abbi2i
    eqtr4i
end
