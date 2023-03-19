include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cgrp.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "csn.mm"
include "cxp.mm"
include "cphtpc.mm"
include "cec.mm"
include "c0g.mm"
include "wceq.mm"
include "cbs.mm"
include "eqid.mm"
include "simpl.mm"
include "simpr.mm"
include "pi1grplem.mm"
include "simpld.mm"

theorem pi1grp
  let cG: class G
  let cJ: class J
  let cX: class X
  let cY: class Y
  let cF: class F
  let vx: setvar x
  let wph: wff ph
  assume pi1grp.2: |- G = ( J pi1 Y )


  assert |- ( ( J e. ( TopOn ` X ) /\ Y e. X ) -> G e. Grp )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cY
    cX
    wcel
    #
    wa
    #
    cG
    cgrp
    wcel
    cc0
    c1
    cicc
    co
    cY
    csn
    cxp
    #
    cJ
    cphtpc
    cfv
    cec
    cG
    c0g
    cfv
    wceq
    @2
    cG
    cbs
    cfv
    #
    cG
    cJ
    cX
    cY
    @3
    pi1grp.2
    @4
    eqid
    @0
    @1
    simpl
    @0
    @1
    simpr
    @3
    eqid
    pi1grplem
    simpld
end
