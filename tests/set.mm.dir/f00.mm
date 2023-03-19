include "c0.mm"
include "wf.mm"
include "wceq.mm"
include "wa.mm"
include "wfn.mm"
include "wfun.mm"
include "cdm.mm"
include "ffun.mm"
include "crn.mm"
include "wss.mm"
include "frn.mm"
include "ss0.mm"
include "syl.mm"
include "dm0rn0.mm"
include "sylibr.mm"
include "df-fn.mm"
include "sylanbrc.mm"
include "fn0.mm"
include "sylib.mm"
include "fdm.mm"
include "eqtr3d.mm"
include "jca.mm"
include "f0.mm"
include "feq1.mm"
include "feq2.mm"
include "sylan9bb.mm"
include "mpbiri.mm"
include "impbii.mm"

theorem f00
  let cA: class A
  let cF: class F


  assert |- ( F : A --> (/) <-> ( F = (/) /\ A = (/) ) )

  proof
    cA
    c0
    cF
    wf
    #
    cF
    c0
    wceq
    #
    cA
    c0
    wceq
    #
    wa
    #
    @0
    @1
    @2
    @0
    cF
    c0
    wfn
    #
    @1
    @0
    cF
    wfun
    cF
    cdm
    #
    c0
    wceq
    #
    @4
    cA
    c0
    cF
    ffun
    @0
    cF
    crn
    #
    c0
    wceq
    #
    @6
    @0
    @7
    c0
    wss
    @8
    cA
    c0
    cF
    frn
    @7
    ss0
    syl
    cF
    dm0rn0
    sylibr
    #
    cF
    c0
    df-fn
    sylanbrc
    cF
    fn0
    sylib
    @0
    @5
    cA
    c0
    cA
    c0
    cF
    fdm
    @9
    eqtr3d
    jca
    @3
    @0
    c0
    c0
    c0
    wf
    #
    c0
    f0
    @1
    @0
    cA
    c0
    c0
    wf
    @2
    @10
    cA
    c0
    cF
    c0
    feq1
    cA
    c0
    c0
    c0
    feq2
    sylan9bb
    mpbiri
    impbii
end
