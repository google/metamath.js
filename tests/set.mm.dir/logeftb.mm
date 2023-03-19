include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "clog.mm"
include "crn.mm"
include "cfv.mm"
include "wceq.mm"
include "ce.mm"
include "wb.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "eldifsn.mm"
include "cres.mm"
include "ccnv.mm"
include "fvres.mm"
include "eqeq1d.mm"
include "adantr.mm"
include "wf1o.mm"
include "eff1o2.mm"
include "f1ocnvfvb.mm"
include "mp3an1.mm"
include "bitr3d.mm"
include "ancoms.mm"
include "dflog2.mm"
include "fveq1i.mm"
include "eqeq1i.mm"
include "syl6rbbr.mm"
include "sylanbr.mm"
include "3impa.mm"

theorem logeftb
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ A =/= 0 /\ B e. ran log ) -> ( ( log ` A ) = B <-> ( exp ` B ) = A ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    cB
    clog
    crn
    #
    wcel
    #
    cA
    clog
    cfv
    #
    cB
    wceq
    #
    cB
    ce
    cfv
    #
    cA
    wceq
    #
    wb
    #
    @0
    @1
    wa
    cA
    cc
    cc0
    csn
    cdif
    #
    wcel
    #
    @3
    @8
    cA
    cc
    cc0
    eldifsn
    @10
    @3
    wa
    @7
    cA
    ce
    @2
    cres
    #
    ccnv
    #
    cfv
    #
    cB
    wceq
    #
    @5
    @3
    @10
    @7
    @14
    wb
    @3
    @10
    wa
    cB
    @11
    cfv
    #
    cA
    wceq
    #
    @7
    @14
    @3
    @16
    @7
    wb
    @10
    @3
    @15
    @6
    cA
    cB
    @2
    ce
    fvres
    eqeq1d
    adantr
    @2
    @9
    @11
    wf1o
    @3
    @10
    @16
    @14
    wb
    eff1o2
    @2
    @9
    cB
    cA
    @11
    f1ocnvfvb
    mp3an1
    bitr3d
    ancoms
    @4
    @13
    cB
    cA
    clog
    @12
    dflog2
    fveq1i
    eqeq1i
    syl6rbbr
    sylanbr
    3impa
end
