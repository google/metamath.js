include "wfun.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "csn.mm"
include "cima.mm"
include "cuni.mm"
include "wceq.mm"
include "wa.mm"
include "fvex.mm"
include "unisn.mm"
include "wfn.mm"
include "eqid.mm"
include "df-fn.mm"
include "mpbiran2.mm"
include "fnsnfv.mm"
include "sylanbr.mm"
include "unieqd.mm"
include "syl5eqr.mm"
include "ex.mm"
include "wn.mm"
include "c0.mm"
include "ndmfv.mm"
include "ndmima.mm"
include "uni0.mm"
include "syl6eq.mm"
include "eqtr4d.mm"
include "pm2.61d1.mm"

theorem funfv
  let cA: class A
  let cF: class F


  assert |- ( Fun F -> ( F ` A ) = U. ( F " { A } ) )

  proof
    cF
    wfun
    #
    cA
    cF
    cdm
    #
    wcel
    #
    cA
    cF
    cfv
    #
    cF
    cA
    csn
    cima
    #
    cuni
    #
    wceq
    #
    @0
    @2
    @6
    @0
    @2
    wa
    #
    @3
    @3
    csn
    #
    cuni
    @5
    @3
    cA
    cF
    fvex
    unisn
    @7
    @8
    @4
    @0
    cF
    @1
    wfn
    #
    @2
    @8
    @4
    wceq
    @9
    @0
    @1
    @1
    wceq
    @1
    eqid
    cF
    @1
    df-fn
    mpbiran2
    @1
    cA
    cF
    fnsnfv
    sylanbr
    unieqd
    syl5eqr
    ex
    @2
    wn
    #
    @3
    c0
    @5
    cA
    cF
    ndmfv
    @10
    @5
    c0
    cuni
    c0
    @10
    @4
    c0
    cA
    cF
    ndmima
    unieqd
    uni0
    syl6eq
    eqtr4d
    pm2.61d1
end
