include "wf1o.mm"
include "wcel.mm"
include "wa.mm"
include "ccnv.mm"
include "ccom.mm"
include "cfv.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "f1ococnv2.mm"
include "fveq1d.mm"
include "adantr.mm"
include "wf.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "syl.mm"
include "fvco3.mm"
include "sylan.mm"
include "fvresi.mm"
include "adantl.mm"
include "3eqtr3d.mm"

theorem f1ocnvfv2
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( ( F : A -1-1-onto-> B /\ C e. B ) -> ( F ` ( `' F ` C ) ) = C )

  proof
    cA
    cB
    cF
    wf1o
    #
    cC
    cB
    wcel
    #
    wa
    cC
    cF
    cF
    ccnv
    #
    ccom
    #
    cfv
    #
    cC
    cid
    cB
    cres
    #
    cfv
    #
    cC
    @2
    cfv
    cF
    cfv
    #
    cC
    @0
    @4
    @6
    wceq
    @1
    @0
    cC
    @3
    @5
    cA
    cB
    cF
    f1ococnv2
    fveq1d
    adantr
    @0
    cB
    cA
    @2
    wf
    #
    @1
    @4
    @7
    wceq
    @0
    cB
    cA
    @2
    wf1o
    @8
    cA
    cB
    cF
    f1ocnv
    cB
    cA
    @2
    f1of
    syl
    cB
    cA
    cC
    cF
    @2
    fvco3
    sylan
    @1
    @6
    cC
    wceq
    @0
    cB
    cC
    fvresi
    adantl
    3eqtr3d
end
