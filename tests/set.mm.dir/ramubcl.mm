include "cn0.mm"
include "wcel.mm"
include "wf.mm"
include "w3a.mm"
include "cram.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cpnf.mm"
include "csn.mm"
include "wceq.mm"
include "wn.mm"
include "cr.mm"
include "nn0re.mm"
include "clt.mm"
include "ltpnf.mm"
include "cxr.mm"
include "wb.mm"
include "rexr.mm"
include "pnfxr.mm"
include "xrltnle.mm"
include "sylancl.mm"
include "mpbid.mm"
include "syl.mm"
include "ad2antrl.mm"
include "simprr.mm"
include "breq1.mm"
include "syl5ibcom.mm"
include "mtod.mm"
include "elsni.mm"
include "nsyl.mm"
include "cun.mm"
include "wo.mm"
include "ramcl2.mm"
include "adantr.mm"
include "elun.mm"
include "sylib.mm"
include "ord.mm"
include "mt3d.mm"

theorem ramubcl
  let cA: class A
  let cR: class R
  let cF: class F
  let cM: class M
  let cV: class V


  assert |- ( ( ( M e. NN0 /\ R e. V /\ F : R --> NN0 ) /\ ( A e. NN0 /\ ( M Ramsey F ) <_ A ) ) -> ( M Ramsey F ) e. NN0 )

  proof
    cM
    cn0
    wcel
    cR
    cV
    wcel
    cR
    cn0
    cF
    wf
    w3a
    #
    cA
    cn0
    wcel
    #
    cM
    cF
    cram
    co
    #
    cA
    cle
    wbr
    #
    wa
    #
    wa
    #
    @2
    cn0
    wcel
    #
    @2
    cpnf
    csn
    #
    wcel
    #
    @5
    @2
    cpnf
    wceq
    #
    @8
    @5
    @9
    cpnf
    cA
    cle
    wbr
    #
    @1
    @10
    wn
    #
    @0
    @3
    @1
    cA
    cr
    wcel
    #
    @11
    cA
    nn0re
    @12
    cA
    cpnf
    clt
    wbr
    #
    @11
    cA
    ltpnf
    @12
    cA
    cxr
    wcel
    cpnf
    cxr
    wcel
    @13
    @11
    wb
    cA
    rexr
    pnfxr
    cA
    cpnf
    xrltnle
    sylancl
    mpbid
    syl
    ad2antrl
    @5
    @3
    @9
    @10
    @0
    @1
    @3
    simprr
    @2
    cpnf
    cA
    cle
    breq1
    syl5ibcom
    mtod
    @2
    cpnf
    elsni
    nsyl
    @5
    @6
    @8
    @5
    @2
    cn0
    @7
    cun
    wcel
    #
    @6
    @8
    wo
    @0
    @14
    @4
    cR
    cF
    cM
    cV
    ramcl2
    adantr
    @2
    cn0
    @7
    elun
    sylib
    ord
    mt3d
end
