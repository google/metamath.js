include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "ccnfld.mm"
include "cgsu.mm"
include "cmpt.mm"
include "c0g.mm"
include "csupp.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cmnf.mm"
include "cgrp.mm"
include "cbs.mm"
include "wceq.mm"
include "ringgrp.mm"
include "mplgrp.mm"
include "sylan2.mm"
include "eqid.mm"
include "grpidcl.mm"
include "mdegval.mm"
include "3syl.mm"
include "c0.mm"
include "csn.mm"
include "cxp.mm"
include "simpl.mm"
include "adantl.mm"
include "mpl0.mm"
include "wfn.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "fnconstg.mm"
include "mp1i.mm"
include "fneq1d.mm"
include "mpbird.mm"
include "ovex.mm"
include "rabex.mm"
include "a1i.mm"
include "fnsuppeq0.mm"
include "syl3anc.mm"
include "imaeq2d.mm"
include "ima0.mm"
include "syl6eq.mm"
include "supeq1d.mm"
include "xrsup0.mm"
include "eqtrd.mm"

theorem mdeg0
  let cD: class D
  let cP: class P
  let cR: class R
  let cI: class I
  let cV: class V
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume mdeg0.d: |- D = ( I mDeg R )
  assume mdeg0.p: |- P = ( I mPoly R )
  assume mdeg0.z: |- .0. = ( 0g ` P )


  assert |- ( ( I e. V /\ R e. Ring ) -> ( D ` .0. ) = -oo )

  proof
    cI
    cV
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    c.0
    cD
    cfv
    #
    vy
    vx
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    #
    vx
    cn0
    cI
    cmap
    co
    #
    crab
    #
    ccnfld
    vy
    cv
    cgsu
    co
    cmpt
    #
    c.0
    cR
    c0g
    cfv
    #
    csupp
    co
    #
    cima
    #
    cxr
    clt
    csup
    #
    cmnf
    @2
    cP
    cgrp
    wcel
    #
    c.0
    cP
    cbs
    cfv
    #
    wcel
    @3
    @11
    wceq
    @1
    @0
    cR
    cgrp
    wcel
    #
    @12
    cR
    ringgrp
    #
    cP
    cR
    cI
    cV
    mdeg0.p
    mplgrp
    sylan2
    @13
    cP
    c.0
    @13
    eqid
    #
    mdeg0.z
    grpidcl
    @6
    @13
    cD
    cP
    cR
    vy
    vx
    c.0
    @7
    cI
    @8
    mdeg0.d
    mdeg0.p
    @16
    @8
    eqid
    #
    @6
    eqid
    #
    @7
    eqid
    mdegval
    3syl
    @2
    @11
    c0
    cxr
    clt
    csup
    cmnf
    @2
    cxr
    @10
    c0
    clt
    @2
    @10
    @7
    c0
    cima
    c0
    @2
    @9
    c0
    @7
    @2
    @9
    c0
    wceq
    #
    c.0
    @6
    @8
    csn
    cxp
    #
    wceq
    #
    @2
    @6
    cP
    cR
    vx
    cI
    @8
    cV
    c.0
    mdeg0.p
    @18
    @17
    mdeg0.z
    @0
    @1
    simpl
    @1
    @14
    @0
    @15
    adantl
    mpl0
    #
    @2
    c.0
    @6
    wfn
    #
    @6
    cvv
    wcel
    #
    @8
    cvv
    wcel
    #
    @19
    @21
    wb
    @2
    @23
    @20
    @6
    wfn
    #
    @25
    @26
    @2
    cR
    c0g
    fvex
    #
    @6
    @8
    cvv
    fnconstg
    mp1i
    @2
    @6
    c.0
    @20
    @22
    fneq1d
    mpbird
    @24
    @2
    @4
    vx
    @5
    cn0
    cI
    cmap
    ovex
    rabex
    a1i
    @25
    @2
    @27
    a1i
    @6
    c.0
    cvv
    cvv
    @8
    fnsuppeq0
    syl3anc
    mpbird
    imaeq2d
    @7
    ima0
    syl6eq
    supeq1d
    xrsup0
    syl6eq
    eqtrd
end
