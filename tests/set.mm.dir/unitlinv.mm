include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "co.mm"
include "cmgp.mm"
include "cress.mm"
include "c0g.mm"
include "cgrp.mm"
include "wceq.mm"
include "eqid.mm"
include "unitgrp.mm"
include "unitgrpbas.mm"
include "cvv.mm"
include "cplusg.mm"
include "cui.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mgpplusg.mm"
include "ressplusg.mm"
include "ax-mp.mm"
include "invrfval.mm"
include "grplinv.mm"
include "sylan.mm"
include "unitgrpid.mm"
include "adantr.mm"
include "eqtr4d.mm"

theorem unitlinv
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let c.1: class .1.
  let cI: class I
  let cX: class X
  assume unitinvcl.1: |- U = ( Unit ` R )
  assume unitinvcl.2: |- I = ( invr ` R )
  assume unitinvcl.3: |- .x. = ( .r ` R )
  assume unitinvcl.4: |- .1. = ( 1r ` R )


  assert |- ( ( R e. Ring /\ X e. U ) -> ( ( I ` X ) .x. X ) = .1. )

  proof
    cR
    crg
    wcel
    #
    cX
    cU
    wcel
    #
    wa
    cX
    cI
    cfv
    cX
    c.x
    co
    #
    cR
    cmgp
    cfv
    #
    cU
    cress
    co
    #
    c0g
    cfv
    #
    c.1
    @0
    @4
    cgrp
    wcel
    @1
    @2
    @5
    wceq
    cR
    cU
    @4
    unitinvcl.1
    @4
    eqid
    #
    unitgrp
    cU
    c.x
    @4
    cI
    cX
    @5
    cR
    cU
    @4
    unitinvcl.1
    @6
    unitgrpbas
    cU
    cvv
    wcel
    c.x
    @4
    cplusg
    cfv
    wceq
    cU
    cR
    cui
    cfv
    cvv
    unitinvcl.1
    cR
    cui
    fvex
    eqeltri
    cU
    c.x
    @3
    @4
    cvv
    @6
    cR
    c.x
    @3
    @3
    eqid
    unitinvcl.3
    mgpplusg
    ressplusg
    ax-mp
    @5
    eqid
    cR
    cU
    @4
    cI
    unitinvcl.1
    @6
    unitinvcl.2
    invrfval
    grplinv
    sylan
    @0
    c.1
    @5
    wceq
    @1
    cR
    cU
    c.1
    @4
    unitinvcl.1
    @6
    unitinvcl.4
    unitgrpid
    adantr
    eqtr4d
end
