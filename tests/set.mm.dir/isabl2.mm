include "cabl.mm"
include "wcel.mm"
include "cgrp.mm"
include "ccmn.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "isabl.mm"
include "cmnd.mm"
include "wb.mm"
include "grpmnd.mm"
include "iscmn.mm"
include "baib.mm"
include "syl.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem isabl2
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let vg: setvar g
  assume iscmn.b: |- B = ( Base ` G )
  assume iscmn.p: |- .+ = ( +g ` G )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint G x
  disjoint G y
  disjoint g x
  disjoint g y
  disjoint B g
  disjoint G g
  disjoint .+ g
  assert |- ( G e. Abel <-> ( G e. Grp /\ A. x e. B A. y e. B ( x .+ y ) = ( y .+ x ) ) )

  proof
    cG
    cabl
    wcel
    cG
    cgrp
    wcel
    #
    cG
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
    c.pl
    co
    @3
    @2
    c.pl
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
    cG
    isabl
    @0
    @1
    @4
    @0
    cG
    cmnd
    wcel
    #
    @1
    @4
    wb
    cG
    grpmnd
    @1
    @5
    @4
    vx
    vy
    cB
    c.pl
    cG
    iscmn.b
    iscmn.p
    iscmn
    baib
    syl
    pm5.32i
    bitri
end
