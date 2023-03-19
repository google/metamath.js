include "cga.mm"
include "co.mm"
include "wcel.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "wfo.mm"
include "gaf.mm"
include "wa.mm"
include "c0g.mm"
include "cfv.mm"
include "cgrp.mm"
include "gagrp.mm"
include "adantr.mm"
include "eqid.mm"
include "grpidcl.mm"
include "syl.mm"
include "simpr.mm"
include "gagrpid.mm"
include "eqcomd.mm"
include "rspceov.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "foov.mm"
include "sylanbrc.mm"

theorem gafo
  let c.po: class .(+)
  let cG: class G
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume gaf.1: |- X = ( Base ` G )


  assert |- ( .(+) e. ( G GrpAct Y ) -> .(+) : ( X X. Y ) -onto-> Y )

  proof
    c.po
    cG
    cY
    cga
    co
    wcel
    #
    cX
    cY
    cxp
    #
    cY
    c.po
    wf
    vx
    cv
    #
    vy
    cv
    vz
    cv
    c.po
    co
    wceq
    vz
    cY
    wrex
    vy
    cX
    wrex
    #
    vx
    cY
    wral
    @1
    cY
    c.po
    wfo
    c.po
    cG
    cX
    cY
    gaf.1
    gaf
    @0
    @3
    vx
    cY
    @0
    @2
    cY
    wcel
    #
    wa
    #
    cG
    c0g
    cfv
    #
    cX
    wcel
    #
    @4
    @2
    @6
    @2
    c.po
    co
    #
    wceq
    @3
    @5
    cG
    cgrp
    wcel
    #
    @7
    @0
    @9
    @4
    c.po
    cG
    cY
    gagrp
    adantr
    cX
    cG
    @6
    gaf.1
    @6
    eqid
    #
    grpidcl
    syl
    @0
    @4
    simpr
    @5
    @8
    @2
    @2
    c.po
    cG
    cY
    @6
    @10
    gagrpid
    eqcomd
    vy
    vz
    cX
    cY
    @6
    @2
    @2
    c.po
    rspceov
    syl3anc
    ralrimiva
    vy
    vz
    vx
    cX
    cY
    cY
    c.po
    foov
    sylanbrc
end
