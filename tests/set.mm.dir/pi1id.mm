include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cgrp.mm"
include "cphtpc.mm"
include "cec.mm"
include "c0g.mm"
include "wceq.mm"
include "cbs.mm"
include "eqid.mm"
include "simpl.mm"
include "simpr.mm"
include "pi1grplem.mm"
include "simprd.mm"

theorem pi1id
  let cG: class G
  let cJ: class J
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cF: class F
  let vx: setvar x
  let wph: wff ph
  assume pi1grp.2: |- G = ( J pi1 Y )
  assume pi1id.3: |- .0. = ( ( 0 [,] 1 ) X. { Y } )


  assert |- ( ( J e. ( TopOn ` X ) /\ Y e. X ) -> [ .0. ] ( ~=ph ` J ) = ( 0g ` G ) )

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
    c.0
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
    c.0
    pi1grp.2
    @3
    eqid
    @0
    @1
    simpl
    @0
    @1
    simpr
    pi1id.3
    pi1grplem
    simprd
end
