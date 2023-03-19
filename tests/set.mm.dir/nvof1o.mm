include "wfn.mm"
include "ccnv.mm"
include "wceq.mm"
include "wa.mm"
include "wf1.mm"
include "wfo.mm"
include "wf1o.mm"
include "wf.mm"
include "wfun.mm"
include "cdm.mm"
include "crn.mm"
include "fnfun.mm"
include "fdmrn.mm"
include "sylib.mm"
include "adantr.mm"
include "fndm.mm"
include "df-rn.mm"
include "dmeq.mm"
include "syl5eq.mm"
include "sylan9eqr.mm"
include "feq23d.mm"
include "mpbid.mm"
include "wb.mm"
include "funeq.mm"
include "adantl.mm"
include "mpbird.mm"
include "df-f1.mm"
include "sylanbrc.mm"
include "simpl.mm"
include "df-fo.mm"
include "df-f1o.mm"

theorem nvof1o
  let cA: class A
  let cF: class F


  assert |- ( ( F Fn A /\ `' F = F ) -> F : A -1-1-onto-> A )

  proof
    cF
    cA
    wfn
    #
    cF
    ccnv
    #
    cF
    wceq
    #
    wa
    #
    cA
    cA
    cF
    wf1
    #
    cA
    cA
    cF
    wfo
    #
    cA
    cA
    cF
    wf1o
    @3
    cA
    cA
    cF
    wf
    #
    @1
    wfun
    #
    @4
    @3
    cF
    cdm
    #
    cF
    crn
    #
    cF
    wf
    #
    @6
    @0
    @10
    @2
    @0
    cF
    wfun
    #
    @10
    cA
    cF
    fnfun
    #
    cF
    fdmrn
    sylib
    adantr
    @3
    @8
    @9
    cA
    cA
    cF
    @0
    @8
    cA
    wceq
    @2
    cA
    cF
    fndm
    #
    adantr
    @2
    @0
    @9
    @8
    cA
    @2
    @9
    @1
    cdm
    @8
    cF
    df-rn
    @1
    cF
    dmeq
    syl5eq
    @13
    sylan9eqr
    #
    feq23d
    mpbid
    @3
    @7
    @11
    @0
    @11
    @2
    @12
    adantr
    @2
    @7
    @11
    wb
    @0
    @1
    cF
    funeq
    adantl
    mpbird
    cA
    cA
    cF
    df-f1
    sylanbrc
    @3
    @0
    @9
    cA
    wceq
    @5
    @0
    @2
    simpl
    @14
    cA
    cA
    cF
    df-fo
    sylanbrc
    cA
    cA
    cF
    df-f1o
    sylanbrc
end
