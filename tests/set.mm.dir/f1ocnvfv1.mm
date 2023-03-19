include "wf1o.mm"
include "wcel.mm"
include "wa.mm"
include "ccnv.mm"
include "ccom.mm"
include "cfv.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "f1ococnv1.mm"
include "fveq1d.mm"
include "adantr.mm"
include "wf.mm"
include "f1of.mm"
include "fvco3.mm"
include "sylan.mm"
include "fvresi.mm"
include "adantl.mm"
include "3eqtr3d.mm"

theorem f1ocnvfv1
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( ( F : A -1-1-onto-> B /\ C e. A ) -> ( `' F ` ( F ` C ) ) = C )

  proof
    cA
    cB
    cF
    wf1o
    #
    cC
    cA
    wcel
    #
    wa
    cC
    cF
    ccnv
    #
    cF
    ccom
    #
    cfv
    #
    cC
    cid
    cA
    cres
    #
    cfv
    #
    cC
    cF
    cfv
    @2
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
    f1ococnv1
    fveq1d
    adantr
    @0
    cA
    cB
    cF
    wf
    @1
    @4
    @7
    wceq
    cA
    cB
    cF
    f1of
    cA
    cB
    cC
    @2
    cF
    fvco3
    sylan
    @1
    @6
    cC
    wceq
    @0
    cA
    cC
    fvresi
    adantl
    3eqtr3d
end
