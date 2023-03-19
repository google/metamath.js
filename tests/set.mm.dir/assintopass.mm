include "cassintop.mm"
include "cfv.mm"
include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "id.mm"
include "elfvex.mm"
include "casslaw.mm"
include "wbr.mm"
include "wa.mm"
include "assintopasslaw.mm"
include "isasslaw.mm"
include "syl5ibcom.mm"
include "mp2and.mm"

theorem assintopass
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cM: class M
  let c.op: class .o.
  let vk: setvar k

  disjoint M x
  disjoint M y
  disjoint M z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint .o. x
  disjoint .o. y
  disjoint .o. z
  disjoint k x
  assert |- ( .o. e. ( assIntOp ` M ) -> A. x e. M A. y e. M A. z e. M ( ( x .o. y ) .o. z ) = ( x .o. ( y .o. z ) ) )

  proof
    c.op
    cM
    cassintop
    cfv
    #
    wcel
    #
    @1
    cM
    cvv
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    c.op
    co
    vz
    cv
    #
    c.op
    co
    @3
    @4
    @5
    c.op
    co
    c.op
    co
    wceq
    vz
    cM
    wral
    vy
    cM
    wral
    vx
    cM
    wral
    #
    @1
    id
    c.op
    cM
    cassintop
    elfvex
    @1
    c.op
    cM
    casslaw
    wbr
    @1
    @2
    wa
    @6
    cM
    c.op
    assintopasslaw
    vx
    vy
    vz
    cM
    @0
    cvv
    c.op
    isasslaw
    syl5ibcom
    mp2and
end
