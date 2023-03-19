include "wcel.mm"
include "cpw.mm"
include "ccrd.mm"
include "cdm.mm"
include "cin.mm"
include "cdom.mm"
include "wbr.mm"
include "cen.mm"
include "wn.mm"
include "csdm.mm"
include "cfn.mm"
include "cvv.mm"
include "pwexg.mm"
include "inex1g.mm"
include "infpwfidom.mm"
include "3syl.mm"
include "wss.mm"
include "syl.mm"
include "cv.mm"
include "finnum.mm"
include "ssriv.mm"
include "sslin.mm"
include "ax-mp.mm"
include "ssdomg.mm"
include "mpisyl.mm"
include "domtr.mm"
include "syl2anc.mm"
include "wf1o.mm"
include "wex.mm"
include "wf1.mm"
include "cxp.mm"
include "wa.mm"
include "wwe.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "copab.mm"
include "cuni.mm"
include "eqid.mm"
include "fpwwecbv.mm"
include "canthnumlem.mm"
include "f1of1.mm"
include "nsyl.mm"
include "nexdv.mm"
include "ensym.mm"
include "bren.mm"
include "sylib.mm"
include "brsdom.mm"
include "sylanbrc.mm"

theorem canthnum
  let cA: class A
  let cV: class V
  let va: setvar a
  let vf: setvar f
  let vr: setvar r
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A e. V -> A ~< ( ~P A i^i dom card ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cA
    cpw
    #
    ccrd
    cdm
    #
    cin
    #
    cdom
    wbr
    #
    cA
    @3
    cen
    wbr
    #
    wn
    cA
    @3
    csdm
    wbr
    @0
    cA
    @1
    cfn
    cin
    #
    cdom
    wbr
    #
    @6
    @3
    cdom
    wbr
    #
    @4
    @0
    @1
    cvv
    wcel
    #
    @6
    cvv
    wcel
    @7
    cA
    cV
    pwexg
    #
    @1
    cfn
    cvv
    inex1g
    cA
    infpwfidom
    3syl
    @0
    @3
    cvv
    wcel
    #
    @6
    @3
    wss
    #
    @8
    @0
    @9
    @11
    @10
    @1
    @2
    cvv
    inex1g
    syl
    cfn
    @2
    wss
    @12
    vx
    cfn
    @2
    vx
    cv
    #
    finnum
    ssriv
    cfn
    @2
    @1
    sslin
    ax-mp
    @6
    @3
    cvv
    ssdomg
    mpisyl
    cA
    @6
    @3
    domtr
    syl2anc
    @0
    @3
    cA
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    @5
    @0
    @15
    vf
    @0
    @3
    cA
    @14
    wf1
    @15
    va
    vz
    cA
    @13
    cA
    wss
    vr
    cv
    #
    @13
    @13
    cxp
    wss
    wa
    @13
    @17
    wwe
    @17
    ccnv
    vy
    cv
    #
    csn
    cima
    @14
    cfv
    @18
    wceq
    vy
    @13
    wral
    wa
    wa
    vx
    vr
    copab
    #
    cdm
    cuni
    #
    @20
    @19
    cfv
    ccnv
    @20
    @14
    cfv
    csn
    cima
    #
    @14
    cV
    @19
    vs
    vx
    vy
    vz
    cA
    @14
    @19
    vs
    vr
    va
    @19
    eqid
    fpwwecbv
    @20
    eqid
    @21
    eqid
    canthnumlem
    @3
    cA
    @14
    f1of1
    nsyl
    nexdv
    @5
    @3
    cA
    cen
    wbr
    @16
    cA
    @3
    ensym
    @3
    cA
    vf
    bren
    sylib
    nsyl
    cA
    @3
    brsdom
    sylanbrc
end
