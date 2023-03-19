include "co.mm"
include "wcel.mm"
include "cop.mm"
include "cxp.mm"
include "wa.mm"
include "cdm.mm"
include "cv.mm"
include "wceq.mm"
include "coprab.mm"
include "cmpt2.mm"
include "df-mpt2.mm"
include "eqtri.mm"
include "dmeqi.mm"
include "dmoprabss.mm"
include "eqsstri.mm"
include "cfv.mm"
include "elfvdm.mm"
include "df-ov.mm"
include "eleq2s.mm"
include "sseldi.mm"
include "opelxp.mm"
include "sylib.mm"

theorem elmpt2cl
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cT: class T
  let cF: class F
  let cX: class X
  let vz: setvar z
  assume elmpt2cl.f: |- F = ( x e. A , y e. B |-> C )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint A z
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint C z
  assert |- ( X e. ( S F T ) -> ( S e. A /\ T e. B ) )

  proof
    cX
    cS
    cT
    cF
    co
    #
    wcel
    #
    cS
    cT
    cop
    #
    cA
    cB
    cxp
    #
    wcel
    cS
    cA
    wcel
    cT
    cB
    wcel
    wa
    @1
    cF
    cdm
    #
    @3
    @2
    @4
    vx
    cv
    cA
    wcel
    vy
    cv
    cB
    wcel
    wa
    vz
    cv
    cC
    wceq
    #
    wa
    vx
    vy
    vz
    coprab
    #
    cdm
    @3
    cF
    @6
    cF
    vx
    vy
    cA
    cB
    cC
    cmpt2
    @6
    elmpt2cl.f
    vx
    vy
    vz
    cA
    cB
    cC
    df-mpt2
    eqtri
    dmeqi
    @5
    vx
    vy
    vz
    cA
    cB
    dmoprabss
    eqsstri
    @2
    @4
    wcel
    cX
    @2
    cF
    cfv
    @0
    cX
    @2
    cF
    elfvdm
    cS
    cT
    cF
    df-ov
    eleq2s
    sseldi
    cS
    cT
    cA
    cB
    opelxp
    sylib
end
