include "cmnd.mm"
include "wcel.mm"
include "wa.mm"
include "c0g.mm"
include "csn.mm"
include "cxp.mm"
include "ccom.mm"
include "csca.mm"
include "cfv.mm"
include "cprds.mm"
include "co.mm"
include "cvv.mm"
include "eqid.mm"
include "simpr.mm"
include "fvexd.mm"
include "wf.mm"
include "fconst6g.mm"
include "adantr.mm"
include "prds0g.mm"
include "cmpt.mm"
include "cv.mm"
include "elex.mm"
include "ad2antrr.mm"
include "wceq.mm"
include "fconstmpt.mm"
include "a1i.mm"
include "wfn.mm"
include "fn0g.mm"
include "dffn5.mm"
include "sylib.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fmptco.mm"
include "syl6reqr.mm"
include "pwsval.mm"
include "fveq2d.mm"
include "3eqtr4d.mm"

theorem pws0g
  let cR: class R
  let cI: class I
  let cV: class V
  let cY: class Y
  let c.0: class .0.
  let vx: setvar x
  let vr: setvar r
  assume pwsmnd.y: |- Y = ( R ^s I )
  assume pws0g.z: |- .0. = ( 0g ` R )


  assert |- ( ( R e. Mnd /\ I e. V ) -> ( I X. { .0. } ) = ( 0g ` Y ) )

  proof
    cR
    cmnd
    wcel
    #
    cI
    cV
    wcel
    #
    wa
    #
    c0g
    cI
    cR
    csn
    cxp
    #
    ccom
    #
    cR
    csca
    cfv
    #
    @3
    cprds
    co
    #
    c0g
    cfv
    cI
    c.0
    csn
    cxp
    #
    cY
    c0g
    cfv
    @2
    @3
    @5
    cI
    cvv
    cV
    @6
    @6
    eqid
    @0
    @1
    simpr
    @2
    cR
    csca
    fvexd
    @0
    cI
    cmnd
    @3
    wf
    @1
    cI
    cR
    cmnd
    fconst6g
    adantr
    prds0g
    @2
    @4
    vx
    cI
    c.0
    cmpt
    @7
    @2
    vx
    vr
    cI
    cvv
    cR
    vr
    cv
    #
    c0g
    cfv
    #
    c.0
    @3
    c0g
    @0
    cR
    cvv
    wcel
    @1
    vx
    cv
    cI
    wcel
    cR
    cmnd
    elex
    ad2antrr
    @3
    vx
    cI
    cR
    cmpt
    wceq
    @2
    vx
    cI
    cR
    fconstmpt
    a1i
    @2
    c0g
    cvv
    wfn
    #
    c0g
    vr
    cvv
    @9
    cmpt
    wceq
    @10
    @2
    fn0g
    a1i
    vr
    cvv
    c0g
    dffn5
    sylib
    @8
    cR
    wceq
    @9
    cR
    c0g
    cfv
    c.0
    @8
    cR
    c0g
    fveq2
    pws0g.z
    syl6eqr
    fmptco
    vx
    cI
    c.0
    fconstmpt
    syl6reqr
    @2
    cY
    @6
    c0g
    cR
    @5
    cI
    cmnd
    cV
    cY
    pwsmnd.y
    @5
    eqid
    pwsval
    fveq2d
    3eqtr4d
end
