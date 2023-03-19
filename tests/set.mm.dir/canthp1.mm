include "c1o.mm"
include "csdm.mm"
include "wbr.mm"
include "ccda.mm"
include "co.mm"
include "cpw.mm"
include "cdom.mm"
include "cen.mm"
include "wn.mm"
include "c2o.mm"
include "1sdom2.mm"
include "sdomdom.mm"
include "cdadom2.mm"
include "mp2b.mm"
include "canthp1lem1.mm"
include "domtr.mm"
include "sylancr.mm"
include "wfal.mm"
include "fal.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "ensym.mm"
include "bren.mm"
include "sylib.mm"
include "wa.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "wf.mm"
include "f1of.mm"
include "cvv.mm"
include "relsdom.mm"
include "brrelex2i.mm"
include "pwidg.mm"
include "syl.mm"
include "ffvelrn.mm"
include "syl2anr.mm"
include "cda1dif.mm"
include "wss.mm"
include "cxp.mm"
include "wwe.mm"
include "ccnv.mm"
include "cima.mm"
include "ccom.mm"
include "wceq.mm"
include "c0.mm"
include "cif.mm"
include "cmpt.mm"
include "wral.mm"
include "copab.mm"
include "cdm.mm"
include "cuni.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "eqeq1.mm"
include "id.mm"
include "ifbieq2d.mm"
include "cbvmptv.mm"
include "coeq2i.mm"
include "eqid.mm"
include "fpwwecbv.mm"
include "canthp1lem2.mm"
include "pm2.21i.mm"
include "exlimddv.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5.mm"
include "mtoi.mm"
include "brsdom.mm"
include "sylanbrc.mm"

theorem canthp1
  let cA: class A
  let va: setvar a
  let vf: setvar f
  let vg: setvar g
  let vr: setvar r
  let vs: setvar s
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( 1o ~< A -> ( A +c 1o ) ~< ~P A )

  proof
    c1o
    cA
    csdm
    wbr
    #
    cA
    c1o
    ccda
    co
    #
    cA
    cpw
    #
    cdom
    wbr
    #
    @1
    @2
    cen
    wbr
    #
    wn
    @1
    @2
    csdm
    wbr
    @0
    @1
    cA
    c2o
    ccda
    co
    #
    cdom
    wbr
    #
    @5
    @2
    cdom
    wbr
    @3
    c1o
    c2o
    csdm
    wbr
    c1o
    c2o
    cdom
    wbr
    @6
    1sdom2
    c1o
    c2o
    sdomdom
    c1o
    c2o
    cA
    cdadom2
    mp2b
    cA
    canthp1lem1
    @1
    @5
    @2
    domtr
    sylancr
    @0
    @4
    wfal
    fal
    @4
    @2
    @1
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    @0
    wfal
    @4
    @2
    @1
    cen
    wbr
    @9
    @1
    @2
    ensym
    @2
    @1
    vf
    bren
    sylib
    @0
    @8
    wfal
    vf
    @0
    @8
    wfal
    @0
    @8
    wa
    #
    @1
    cA
    @7
    cfv
    #
    csn
    cdif
    #
    cA
    vg
    cv
    #
    wf1o
    #
    wfal
    vg
    @10
    @12
    cA
    cen
    wbr
    #
    @14
    vg
    wex
    @10
    @11
    @1
    wcel
    #
    @15
    @8
    @2
    @1
    @7
    wf
    cA
    @2
    wcel
    #
    @16
    @0
    @2
    @1
    @7
    f1of
    @0
    cA
    cvv
    wcel
    @17
    c1o
    cA
    csdm
    relsdom
    brrelex2i
    cA
    cvv
    pwidg
    syl
    @2
    @1
    cA
    @7
    ffvelrn
    syl2anr
    cA
    @11
    cda1dif
    syl
    @12
    cA
    vg
    bren
    sylib
    @10
    @14
    wa
    #
    wfal
    @18
    vx
    vy
    cA
    va
    cv
    #
    cA
    wss
    vs
    cv
    #
    @19
    @19
    cxp
    wss
    wa
    @19
    @20
    wwe
    @20
    ccnv
    vz
    cv
    #
    csn
    cima
    @13
    @7
    ccom
    #
    vw
    @2
    vw
    cv
    #
    cA
    wceq
    #
    c0
    @23
    cif
    #
    cmpt
    #
    ccom
    #
    cfv
    @21
    wceq
    vz
    @19
    wral
    wa
    wa
    va
    vs
    copab
    #
    cdm
    cuni
    #
    @7
    @13
    @27
    @28
    vr
    @0
    @8
    @14
    simpll
    @0
    @8
    @14
    simplr
    @10
    @14
    simpr
    @26
    vx
    @2
    vx
    cv
    #
    cA
    wceq
    #
    c0
    @30
    cif
    #
    cmpt
    @22
    vw
    vx
    @2
    @25
    @32
    @23
    @30
    wceq
    #
    @24
    @31
    @23
    @30
    c0
    @23
    @30
    cA
    eqeq1
    @33
    id
    ifbieq2d
    cbvmptv
    coeq2i
    va
    vz
    vy
    cA
    @27
    @28
    vr
    vs
    vx
    @28
    eqid
    fpwwecbv
    @29
    eqid
    canthp1lem2
    pm2.21i
    exlimddv
    ex
    exlimdv
    syl5
    mtoi
    @1
    @2
    brsdom
    sylanbrc
end
