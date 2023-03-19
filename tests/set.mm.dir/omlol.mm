include "coml.mm"
include "wcel.mm"
include "col.mm"
include "cv.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "coc.mm"
include "cmee.mm"
include "co.mm"
include "cjn.mm"
include "wceq.mm"
include "wi.mm"
include "cbs.mm"
include "wral.mm"
include "eqid.mm"
include "isoml.mm"
include "simplbi.mm"

theorem omlol
  let cK: class K
  let vx: setvar x
  let vy: setvar y


  assert |- ( K e. OML -> K e. OL )

  proof
    cK
    coml
    wcel
    cK
    col
    wcel
    vx
    cv
    #
    vy
    cv
    #
    cK
    cple
    cfv
    #
    wbr
    @1
    @0
    @1
    @0
    cK
    coc
    cfv
    #
    cfv
    cK
    cmee
    cfv
    #
    co
    cK
    cjn
    cfv
    #
    co
    wceq
    wi
    vy
    cK
    cbs
    cfv
    #
    wral
    vx
    @6
    wral
    vx
    vy
    @6
    @5
    cK
    @2
    @4
    @3
    @6
    eqid
    @2
    eqid
    @5
    eqid
    @4
    eqid
    @3
    eqid
    isoml
    simplbi
end
