include "wf1o.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crio.mm"
include "ccnv.mm"
include "f1ocnvdm.mm"
include "wb.mm"
include "f1ocnvfvb.mm"
include "3expa.mm"
include "an32s.mm"
include "eqcom.mm"
include "syl6bbr.mm"
include "riota5.mm"
include "eqcomd.mm"

theorem f1ocnvfv3
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint F x
  assert |- ( ( F : A -1-1-onto-> B /\ C e. B ) -> ( `' F ` C ) = ( iota_ x e. A ( F ` x ) = C ) )

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
    #
    vx
    cv
    #
    cF
    cfv
    cC
    wceq
    #
    vx
    cA
    crio
    cC
    cF
    ccnv
    cfv
    #
    @2
    @4
    vx
    cA
    @5
    cA
    cB
    cC
    cF
    f1ocnvdm
    @2
    @3
    cA
    wcel
    #
    wa
    @4
    @5
    @3
    wceq
    #
    @3
    @5
    wceq
    @0
    @6
    @1
    @4
    @7
    wb
    #
    @0
    @6
    @1
    @8
    cA
    cB
    @3
    cC
    cF
    f1ocnvfvb
    3expa
    an32s
    @3
    @5
    eqcom
    syl6bbr
    riota5
    eqcomd
end
