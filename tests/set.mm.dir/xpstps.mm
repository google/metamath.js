include "ctps.mm"
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
include "wfo.mm"
include "xpsff1o2.mm"
include "a1i.mm"
include "f1ocnv.mm"
include "f1ofo.mm"
include "3syl.mm"
include "c2o.mm"
include "cvv.mm"
include "con0.mm"
include "fvexd.mm"
include "2on.mm"
include "wf.mm"
include "xpscf.mm"
include "biimpri.mm"
include "prdstps.mm"
include "imastps.mm"

theorem xpstps
  let cR: class R
  let cS: class S
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  assume xpstps.t: |- T = ( R Xs. S )


  assert |- ( ( R e. TopSp /\ S e. TopSp ) -> T e. TopSp )

  proof
    cR
    ctps
    wcel
    #
    cS
    ctps
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
    ctps
    ctps
    @3
    @4
    xpstps.t
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
    ctps
    ctps
    @3
    @4
    xpstps.t
    @12
    @13
    @14
    @15
    @16
    @17
    @18
    xpslem
    @2
    @5
    @11
    @9
    wf1o
    #
    @11
    @5
    @10
    wf1o
    @11
    @5
    @10
    wfo
    @19
    @2
    vx
    vy
    @3
    @4
    @9
    @16
    xpsff1o2
    a1i
    @5
    @11
    @9
    f1ocnv
    @11
    @5
    @10
    f1ofo
    3syl
    @2
    @7
    @6
    c2o
    cvv
    con0
    @8
    @18
    @2
    cR
    csca
    fvexd
    c2o
    con0
    wcel
    @2
    2on
    a1i
    c2o
    ctps
    @7
    wf
    @2
    ctps
    cR
    cS
    xpscf
    biimpri
    prdstps
    imastps
end
