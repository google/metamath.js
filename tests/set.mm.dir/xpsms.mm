include "cmt.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cxp.mm"
include "csca.mm"
include "csn.mm"
include "ccda.mm"
include "co.mm"
include "ccnv.mm"
include "cprds.mm"
include "cv.mm"
include "cmpt2.mm"
include "crn.mm"
include "eqid.mm"
include "simpl.mm"
include "simpr.mm"
include "xpsval.mm"
include "xpslem.mm"
include "wf1o.mm"
include "xpsff1o2.mm"
include "f1ocnv.mm"
include "mp1i.mm"
include "cvv.mm"
include "c2o.mm"
include "cfn.mm"
include "wf.mm"
include "fvexd.mm"
include "com.mm"
include "2onn.mm"
include "nnfi.mm"
include "xpscf.mm"
include "biimpri.mm"
include "prdsms.mm"
include "syl3anc.mm"
include "imasf1oms.mm"

theorem xpsms
  let cR: class R
  let cS: class S
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  assume xpsms.t: |- T = ( R Xs. S )


  assert |- ( ( R e. MetSp /\ S e. MetSp ) -> T e. MetSp )

  proof
    cR
    cmt
    wcel
    #
    cS
    cmt
    wcel
    #
    wa
    #
    cR
    cbs
    cfv
    #
    cS
    cbs
    cfv
    #
    cxp
    #
    cR
    csca
    cfv
    #
    cR
    csn
    cS
    csn
    ccda
    co
    ccnv
    #
    cprds
    co
    #
    cT
    vx
    vy
    @3
    @4
    vx
    cv
    csn
    vy
    cv
    csn
    ccda
    co
    ccnv
    cmpt2
    #
    ccnv
    #
    @9
    crn
    #
    @2
    vx
    vy
    cR
    cS
    cT
    @8
    @9
    @6
    cmt
    cmt
    @3
    @4
    xpsms.t
    @3
    eqid
    #
    @4
    eqid
    #
    @0
    @1
    simpl
    #
    @0
    @1
    simpr
    #
    @9
    eqid
    #
    @6
    eqid
    #
    @8
    eqid
    #
    xpsval
    @2
    vx
    vy
    cR
    cS
    cT
    @8
    @9
    @6
    cmt
    cmt
    @3
    @4
    xpsms.t
    @12
    @13
    @14
    @15
    @16
    @17
    @18
    xpslem
    @5
    @11
    @9
    wf1o
    @11
    @5
    @10
    wf1o
    @2
    vx
    vy
    @3
    @4
    @9
    @16
    xpsff1o2
    @5
    @11
    @9
    f1ocnv
    mp1i
    @2
    @6
    cvv
    wcel
    c2o
    cfn
    wcel
    #
    c2o
    cmt
    @7
    wf
    #
    @8
    cmt
    wcel
    @2
    cR
    csca
    fvexd
    c2o
    com
    wcel
    @19
    @2
    2onn
    c2o
    nnfi
    mp1i
    @20
    @2
    cmt
    cR
    cS
    xpscf
    biimpri
    @7
    @6
    c2o
    cvv
    @8
    @18
    prdsms
    syl3anc
    imasf1oms
end
