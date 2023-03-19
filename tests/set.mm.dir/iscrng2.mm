include "ccrg.mm"
include "wcel.mm"
include "crg.mm"
include "cmgp.mm"
include "cfv.mm"
include "ccmn.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "eqid.mm"
include "iscrng.mm"
include "cmnd.mm"
include "wb.mm"
include "ringmgp.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "iscmn.mm"
include "baib.mm"
include "syl.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem iscrng2
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let c.x: class .x.
  assume ringcl.b: |- B = ( Base ` R )
  assume ringcl.t: |- .x. = ( .r ` R )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint R x
  disjoint R y
  assert |- ( R e. CRing <-> ( R e. Ring /\ A. x e. B A. y e. B ( x .x. y ) = ( y .x. x ) ) )

  proof
    cR
    ccrg
    wcel
    cR
    crg
    wcel
    #
    cR
    cmgp
    cfv
    #
    ccmn
    wcel
    #
    wa
    @0
    vx
    cv
    #
    vy
    cv
    #
    c.x
    co
    @4
    @3
    c.x
    co
    wceq
    vy
    cB
    wral
    vx
    cB
    wral
    #
    wa
    cR
    @1
    @1
    eqid
    #
    iscrng
    @0
    @2
    @5
    @0
    @1
    cmnd
    wcel
    #
    @2
    @5
    wb
    cR
    @1
    @6
    ringmgp
    @2
    @7
    @5
    vx
    vy
    cB
    c.x
    @1
    cB
    cR
    @1
    @6
    ringcl.b
    mgpbas
    cR
    c.x
    @1
    @6
    ringcl.t
    mgpplusg
    iscmn
    baib
    syl
    pm5.32i
    bitri
end
