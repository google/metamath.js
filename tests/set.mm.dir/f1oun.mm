include "wf1o.mm"
include "wa.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cun.mm"
include "wfn.mm"
include "ccnv.mm"
include "wi.mm"
include "dff1o4.mm"
include "fnun.mm"
include "ex.mm"
include "cnvun.mm"
include "fneq1i.mm"
include "sylibr.mm"
include "im2anan9.mm"
include "an4s.mm"
include "syl2anb.mm"
include "syl6ibr.mm"
include "imp.mm"

theorem f1oun
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G


  assert |- ( ( ( F : A -1-1-onto-> B /\ G : C -1-1-onto-> D ) /\ ( ( A i^i C ) = (/) /\ ( B i^i D ) = (/) ) ) -> ( F u. G ) : ( A u. C ) -1-1-onto-> ( B u. D ) )

  proof
    cA
    cB
    cF
    wf1o
    #
    cC
    cD
    cG
    wf1o
    #
    wa
    #
    cA
    cC
    cin
    c0
    wceq
    #
    cB
    cD
    cin
    c0
    wceq
    #
    wa
    #
    cA
    cC
    cun
    #
    cB
    cD
    cun
    #
    cF
    cG
    cun
    #
    wf1o
    #
    @2
    @5
    @8
    @6
    wfn
    #
    @8
    ccnv
    #
    @7
    wfn
    #
    wa
    #
    @9
    @0
    cF
    cA
    wfn
    #
    cF
    ccnv
    #
    cB
    wfn
    #
    wa
    cG
    cC
    wfn
    #
    cG
    ccnv
    #
    cD
    wfn
    #
    wa
    @5
    @13
    wi
    #
    @1
    cA
    cB
    cF
    dff1o4
    cC
    cD
    cG
    dff1o4
    @14
    @17
    @16
    @19
    @20
    @14
    @17
    wa
    #
    @3
    @10
    @16
    @19
    wa
    #
    @4
    @12
    @21
    @3
    @10
    cA
    cC
    cF
    cG
    fnun
    ex
    @22
    @4
    @12
    @22
    @4
    wa
    @15
    @18
    cun
    #
    @7
    wfn
    @12
    cB
    cD
    @15
    @18
    fnun
    @7
    @11
    @23
    cF
    cG
    cnvun
    fneq1i
    sylibr
    ex
    im2anan9
    an4s
    syl2anb
    @6
    @7
    @8
    dff1o4
    syl6ibr
    imp
end
