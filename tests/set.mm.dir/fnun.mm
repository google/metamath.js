include "wfn.mm"
include "wa.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cun.mm"
include "wfun.mm"
include "cdm.mm"
include "wi.mm"
include "df-fn.mm"
include "ineq12.mm"
include "eqeq1d.mm"
include "anbi2d.mm"
include "funun.mm"
include "syl6bir.mm"
include "dmun.mm"
include "uneq12.mm"
include "syl5eq.mm"
include "jctird.mm"
include "syl6ibr.mm"
include "expd.mm"
include "impcom.mm"
include "an4s.mm"
include "syl2anb.mm"
include "imp.mm"

theorem fnun
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G


  assert |- ( ( ( F Fn A /\ G Fn B ) /\ ( A i^i B ) = (/) ) -> ( F u. G ) Fn ( A u. B ) )

  proof
    cF
    cA
    wfn
    #
    cG
    cB
    wfn
    #
    wa
    cA
    cB
    cin
    #
    c0
    wceq
    #
    cF
    cG
    cun
    #
    cA
    cB
    cun
    #
    wfn
    #
    @0
    cF
    wfun
    #
    cF
    cdm
    #
    cA
    wceq
    #
    wa
    cG
    wfun
    #
    cG
    cdm
    #
    cB
    wceq
    #
    wa
    @3
    @6
    wi
    #
    @1
    cF
    cA
    df-fn
    cG
    cB
    df-fn
    @7
    @10
    @9
    @12
    @13
    @9
    @12
    wa
    #
    @7
    @10
    wa
    #
    @13
    @14
    @15
    @3
    @6
    @14
    @15
    @3
    wa
    #
    @4
    wfun
    #
    @4
    cdm
    #
    @5
    wceq
    #
    wa
    @6
    @14
    @16
    @17
    @19
    @14
    @16
    @15
    @8
    @11
    cin
    #
    c0
    wceq
    #
    wa
    @17
    @14
    @21
    @3
    @15
    @14
    @20
    @2
    c0
    @8
    cA
    @11
    cB
    ineq12
    eqeq1d
    anbi2d
    cF
    cG
    funun
    syl6bir
    @14
    @18
    @8
    @11
    cun
    @5
    cF
    cG
    dmun
    @8
    cA
    @11
    cB
    uneq12
    syl5eq
    jctird
    @4
    @5
    df-fn
    syl6ibr
    expd
    impcom
    an4s
    syl2anb
    imp
end
