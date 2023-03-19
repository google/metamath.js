include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "simpl2.mm"
include "breq1.mm"
include "rspcev.mm"
include "3ad2antl3.mm"
include "wb.mm"
include "simpl1.mm"
include "islvol.mm"
include "syl.mm"
include "mpbir2and.mm"

theorem lvoli
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vy: setvar y
  let vx: setvar x
  assume lvolset.b: |- B = ( Base ` K )
  assume lvolset.c: |- C = ( <o ` K )
  assume lvolset.p: |- P = ( LPlanes ` K )
  assume lvolset.v: |- V = ( LVols ` K )


  assert |- ( ( ( K e. D /\ Y e. B /\ X e. P ) /\ X C Y ) -> Y e. V )

  proof
    cK
    cD
    wcel
    #
    cY
    cB
    wcel
    #
    cX
    cP
    wcel
    #
    w3a
    cX
    cY
    cC
    wbr
    #
    wa
    #
    cY
    cV
    wcel
    #
    @1
    vx
    cv
    #
    cY
    cC
    wbr
    #
    vx
    cP
    wrex
    #
    @0
    @1
    @2
    @3
    simpl2
    @2
    @0
    @3
    @8
    @1
    @7
    @3
    vx
    cX
    cP
    @6
    cX
    cY
    cC
    breq1
    rspcev
    3ad2antl3
    @4
    @0
    @5
    @1
    @8
    wa
    wb
    @0
    @1
    @2
    @3
    simpl1
    vx
    cD
    cB
    cC
    cP
    cK
    cV
    cY
    lvolset.b
    lvolset.c
    lvolset.p
    lvolset.v
    islvol
    syl
    mpbir2and
end
