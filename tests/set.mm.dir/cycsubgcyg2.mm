include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cfv.mm"
include "cress.mm"
include "co.mm"
include "cz.mm"
include "cv.mm"
include "cmg.mm"
include "cmpt.mm"
include "crn.mm"
include "ccyg.mm"
include "eqid.mm"
include "cycsubg2.mm"
include "oveq2d.mm"
include "cycsubgcyg.mm"
include "eqeltrd.mm"

theorem cycsubgcyg2
  let cA: class A
  let cB: class B
  let cG: class G
  let cK: class K
  let vn: setvar n
  assume cycsubgcyg2.b: |- B = ( Base ` G )
  assume cycsubgcyg2.k: |- K = ( mrCls ` ( SubGrp ` G ) )


  assert |- ( ( G e. Grp /\ A e. B ) -> ( G |`s ( K ` { A } ) ) e. CycGrp )

  proof
    cG
    cgrp
    wcel
    cA
    cB
    wcel
    wa
    #
    cG
    cA
    csn
    cK
    cfv
    #
    cress
    co
    cG
    vn
    cz
    vn
    cv
    cA
    cG
    cmg
    cfv
    #
    co
    cmpt
    #
    crn
    #
    cress
    co
    ccyg
    @0
    @1
    @4
    cG
    cress
    vn
    cA
    @2
    @3
    cG
    cK
    cB
    cycsubgcyg2.b
    @2
    eqid
    #
    @3
    eqid
    cycsubgcyg2.k
    cycsubg2
    oveq2d
    vn
    cA
    @4
    @2
    cG
    cB
    cycsubgcyg2.b
    @5
    @4
    eqid
    cycsubgcyg
    eqeltrd
end
