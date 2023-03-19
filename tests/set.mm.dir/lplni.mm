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
include "islpln.mm"
include "syl.mm"
include "mpbir2and.mm"

theorem lplni
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cK: class K
  let cN: class N
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vy: setvar y
  let vx: setvar x
  assume lplnset.b: |- B = ( Base ` K )
  assume lplnset.c: |- C = ( <o ` K )
  assume lplnset.n: |- N = ( LLines ` K )
  assume lplnset.p: |- P = ( LPlanes ` K )


  assert |- ( ( ( K e. D /\ Y e. B /\ X e. N ) /\ X C Y ) -> Y e. P )

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
    cN
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
    cP
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
    cN
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
    cN
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
    cN
    cY
    lplnset.b
    lplnset.c
    lplnset.n
    lplnset.p
    islpln
    syl
    mpbir2and
end
