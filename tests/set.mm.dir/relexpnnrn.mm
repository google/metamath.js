include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "ccnv.mm"
include "crelexp.mm"
include "co.mm"
include "cdm.mm"
include "crn.mm"
include "cvv.mm"
include "wss.mm"
include "cnvexg.mm"
include "relexpnndm.mm"
include "sylan2.mm"
include "df-rn.mm"
include "cn0.mm"
include "wceq.mm"
include "nnnn0.mm"
include "relexpcnv.mm"
include "sylan.mm"
include "dmeqd.mm"
include "syl5eq.mm"
include "a1i.mm"
include "3sstr4d.mm"

theorem relexpnnrn
  let cR: class R
  let cN: class N
  let cV: class V


  assert |- ( ( N e. NN /\ R e. V ) -> ran ( R ^r N ) C_ ran R )

  proof
    cN
    cn
    wcel
    #
    cR
    cV
    wcel
    #
    wa
    #
    cR
    ccnv
    #
    cN
    crelexp
    co
    #
    cdm
    #
    @3
    cdm
    #
    cR
    cN
    crelexp
    co
    #
    crn
    #
    cR
    crn
    #
    @1
    @0
    @3
    cvv
    wcel
    @5
    @6
    wss
    cR
    cV
    cnvexg
    @3
    cN
    cvv
    relexpnndm
    sylan2
    @2
    @8
    @7
    ccnv
    #
    cdm
    @5
    @7
    df-rn
    @2
    @10
    @4
    @0
    cN
    cn0
    wcel
    @1
    @10
    @4
    wceq
    cN
    nnnn0
    cR
    cN
    cV
    relexpcnv
    sylan
    dmeqd
    syl5eq
    @9
    @6
    wceq
    @2
    cR
    df-rn
    a1i
    3sstr4d
end
