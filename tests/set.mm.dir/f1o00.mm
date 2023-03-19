include "c0.mm"
include "wf1o.mm"
include "wfn.mm"
include "ccnv.mm"
include "wa.mm"
include "wceq.mm"
include "dff1o4.mm"
include "fn0.mm"
include "biimpi.mm"
include "adantr.mm"
include "cdm.mm"
include "dm0.mm"
include "cnveq.mm"
include "cnv0.mm"
include "syl6eq.mm"
include "sylbi.mm"
include "fneq1d.mm"
include "biimpa.mm"
include "fndm.mm"
include "syl.mm"
include "syl5reqr.mm"
include "jca.mm"
include "biimpri.mm"
include "eqid.mm"
include "mpbir.mm"
include "fneq2.mm"
include "sylan9bb.mm"
include "mpbiri.mm"
include "impbii.mm"
include "bitri.mm"

theorem f1o00
  let cA: class A
  let cF: class F


  assert |- ( F : (/) -1-1-onto-> A <-> ( F = (/) /\ A = (/) ) )

  proof
    c0
    cA
    cF
    wf1o
    cF
    c0
    wfn
    #
    cF
    ccnv
    #
    cA
    wfn
    #
    wa
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
    c0
    cA
    cF
    dff1o4
    @3
    @6
    @3
    @4
    @5
    @0
    @4
    @2
    @0
    @4
    cF
    fn0
    #
    biimpi
    adantr
    @3
    c0
    c0
    cdm
    #
    cA
    dm0
    @3
    c0
    cA
    wfn
    #
    @8
    cA
    wceq
    @0
    @2
    @9
    @0
    cA
    @1
    c0
    @0
    @4
    @1
    c0
    wceq
    @7
    @4
    @1
    c0
    ccnv
    c0
    cF
    c0
    cnveq
    cnv0
    syl6eq
    #
    sylbi
    fneq1d
    biimpa
    cA
    c0
    fndm
    syl
    syl5reqr
    jca
    @6
    @0
    @2
    @4
    @0
    @5
    @0
    @4
    @7
    biimpri
    adantr
    @6
    @2
    c0
    c0
    wfn
    #
    @11
    c0
    c0
    wceq
    c0
    eqid
    c0
    fn0
    mpbir
    @4
    @2
    @9
    @5
    @11
    @4
    cA
    @1
    c0
    @10
    fneq1d
    cA
    c0
    c0
    fneq2
    sylan9bb
    mpbiri
    jca
    impbii
    bitri
end
