include "cmnd.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "ccda.mm"
include "co.mm"
include "ccnv.mm"
include "cmpt2.mm"
include "csca.mm"
include "cprds.mm"
include "cimas.mm"
include "eqid.mm"
include "simpl.mm"
include "simpr.mm"
include "xpsval.mm"
include "cxp.mm"
include "wf1.mm"
include "wf1o.mm"
include "crn.mm"
include "xpsff1o2.mm"
include "wceq.mm"
include "wb.mm"
include "xpslem.mm"
include "f1oeq3.mm"
include "syl.mm"
include "mpbii.mm"
include "f1ocnv.mm"
include "f1of1.mm"
include "3syl.mm"
include "c2o.mm"
include "cvv.mm"
include "con0.mm"
include "2on.mm"
include "a1i.mm"
include "fvexd.mm"
include "wf.mm"
include "xpscf.mm"
include "biimpri.mm"
include "prdsmndd.mm"
include "imasmndf1.mm"
include "syl2anc.mm"
include "eqeltrd.mm"

theorem xpsmnd
  let cR: class R
  let cS: class S
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  assume xpsmnd.t: |- T = ( R Xs. S )


  assert |- ( ( R e. Mnd /\ S e. Mnd ) -> T e. Mnd )

  proof
    cR
    cmnd
    wcel
    #
    cS
    cmnd
    wcel
    #
    wa
    #
    cT
    vx
    vy
    cR
    cbs
    cfv
    #
    cS
    cbs
    cfv
    #
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
    cimas
    co
    #
    cmnd
    @2
    vx
    vy
    cR
    cS
    cT
    @9
    @5
    @7
    cmnd
    cmnd
    @3
    @4
    xpsmnd.t
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
    @5
    eqid
    #
    @7
    eqid
    #
    @9
    eqid
    #
    xpsval
    @2
    @9
    cbs
    cfv
    #
    @3
    @4
    cxp
    #
    @6
    wf1
    #
    @9
    cmnd
    wcel
    @10
    cmnd
    wcel
    @2
    @19
    @18
    @5
    wf1o
    #
    @18
    @19
    @6
    wf1o
    @20
    @2
    @19
    @5
    crn
    #
    @5
    wf1o
    #
    @21
    vx
    vy
    @3
    @4
    @5
    @15
    xpsff1o2
    @2
    @22
    @18
    wceq
    @23
    @21
    wb
    @2
    vx
    vy
    cR
    cS
    cT
    @9
    @5
    @7
    cmnd
    cmnd
    @3
    @4
    xpsmnd.t
    @11
    @12
    @13
    @14
    @15
    @16
    @17
    xpslem
    @22
    @18
    @19
    @5
    f1oeq3
    syl
    mpbii
    @19
    @18
    @5
    f1ocnv
    @18
    @19
    @6
    f1of1
    3syl
    @2
    @8
    @7
    c2o
    cvv
    con0
    @9
    @17
    c2o
    con0
    wcel
    @2
    2on
    a1i
    @2
    cR
    csca
    fvexd
    c2o
    cmnd
    @8
    wf
    @2
    cmnd
    cR
    cS
    xpscf
    biimpri
    prdsmndd
    @19
    @9
    @10
    @6
    @18
    @10
    eqid
    @18
    eqid
    imasmndf1
    syl2anc
    eqeltrd
end
