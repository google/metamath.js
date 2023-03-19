include "wcel.mm"
include "cts.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cplusg.mm"
include "cpw.mm"
include "csn.mm"
include "cxp.mm"
include "cpt.mm"
include "ctp.mm"
include "eqid.mm"
include "symgbas.mm"
include "symgplusg.mm"
include "symgval.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wceq.mm"
include "fvex.mm"
include "topgrptset.mm"
include "ax-mp.mm"
include "syl6reqr.mm"

theorem symgtset
  let cA: class A
  let cG: class G
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume symggrp.1: |- G = ( SymGrp ` A )


  assert |- ( A e. V -> ( Xt_ ` ( A X. { ~P A } ) ) = ( TopSet ` G ) )

  proof
    cA
    cV
    wcel
    #
    cG
    cts
    cfv
    cnx
    cbs
    cfv
    cG
    cbs
    cfv
    #
    cop
    cnx
    cplusg
    cfv
    cG
    cplusg
    cfv
    #
    cop
    cnx
    cts
    cfv
    cA
    cA
    cpw
    csn
    cxp
    #
    cpt
    cfv
    #
    cop
    ctp
    #
    cts
    cfv
    #
    @4
    @0
    cG
    @5
    cts
    vx
    cA
    @1
    @2
    vf
    vg
    cG
    @4
    cV
    symggrp.1
    vx
    cA
    @1
    cG
    symggrp.1
    @1
    eqid
    #
    symgbas
    cA
    @1
    @2
    vf
    vg
    cG
    symggrp.1
    @7
    @2
    eqid
    symgplusg
    @4
    eqid
    symgval
    fveq2d
    @4
    cvv
    wcel
    @4
    @6
    wceq
    @3
    cpt
    fvex
    @1
    @2
    @4
    @5
    cvv
    @5
    eqid
    topgrptset
    ax-mp
    syl6reqr
end
