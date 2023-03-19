include "wfn.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cres.mm"
include "cdm.mm"
include "cin.mm"
include "wrel.mm"
include "wceq.mm"
include "fnrel.mm"
include "adantr.mm"
include "resindm.mm"
include "eqcomd.mm"
include "syl.mm"
include "wi.mm"
include "wfun.mm"
include "fnfun.mm"
include "funfn.mm"
include "sylib.mm"
include "fnresin2.mm"
include "infi.mm"
include "fnfi.mm"
include "sylan2.mm"
include "ex.mm"
include "3syl.mm"
include "imp.mm"
include "eqeltrd.mm"

theorem resfnfinfin
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( F Fn A /\ B e. Fin ) -> ( F |` B ) e. Fin )

  proof
    cF
    cA
    wfn
    #
    cB
    cfn
    wcel
    #
    wa
    #
    cF
    cB
    cres
    #
    cF
    cB
    cF
    cdm
    #
    cin
    #
    cres
    #
    cfn
    @2
    cF
    wrel
    #
    @3
    @6
    wceq
    @0
    @7
    @1
    cA
    cF
    fnrel
    adantr
    @7
    @6
    @3
    cF
    cB
    resindm
    eqcomd
    syl
    @0
    @1
    @6
    cfn
    wcel
    #
    @0
    cF
    @4
    wfn
    #
    @6
    @5
    wfn
    #
    @1
    @8
    wi
    @0
    cF
    wfun
    @9
    cA
    cF
    fnfun
    cF
    funfn
    sylib
    @4
    cB
    cF
    fnresin2
    @10
    @1
    @8
    @1
    @10
    @5
    cfn
    wcel
    @8
    cB
    @4
    infi
    @5
    @6
    fnfi
    sylan2
    ex
    3syl
    imp
    eqeltrd
end
