include "cprb.mm"
include "wcel.mm"
include "cdm.mm"
include "cuni.mm"
include "wceq.mm"
include "cpw.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wdisj.mm"
include "wa.mm"
include "w3a.mm"
include "cfv.mm"
include "cin.mm"
include "cesum.mm"
include "simp1.mm"
include "simp2.mm"
include "simp32.mm"
include "simp31.mm"
include "simp33l.mm"
include "simp33r.mm"
include "id.mm"
include "cbvdisjv.mm"
include "sylib.mm"
include "totprobd.mm"
include "ineq1.mm"
include "fveq2d.mm"
include "cbvesumv.mm"
include "syl6eqr.mm"

theorem totprob
  let cA: class A
  let cB: class B
  let cP: class P
  let vb: setvar b
  let vc: setvar c

  disjoint A b
  disjoint B b
  disjoint P b
  disjoint b c
  disjoint A c
  disjoint B c
  disjoint P c
  assert |- ( ( P e. Prob /\ A e. dom P /\ ( U. B = U. dom P /\ B e. ~P dom P /\ ( B ~<_ _om /\ Disj_ b e. B b ) ) ) -> ( P ` A ) = sum* b e. B ( P ` ( b i^i A ) ) )

  proof
    cP
    cprb
    wcel
    #
    cA
    cP
    cdm
    #
    wcel
    #
    cB
    cuni
    @1
    cuni
    wceq
    #
    cB
    @1
    cpw
    wcel
    #
    cB
    com
    cdom
    wbr
    #
    vb
    cB
    vb
    cv
    #
    wdisj
    #
    wa
    #
    w3a
    #
    w3a
    #
    cA
    cP
    cfv
    cB
    vc
    cv
    #
    cA
    cin
    #
    cP
    cfv
    #
    vc
    cesum
    cB
    @6
    cA
    cin
    #
    cP
    cfv
    #
    vb
    cesum
    @10
    cA
    cB
    cP
    vc
    @0
    @2
    @9
    simp1
    @0
    @2
    @9
    simp2
    @0
    @2
    @3
    @4
    @8
    simp32
    @0
    @2
    @3
    @4
    @8
    simp31
    @5
    @7
    @3
    @4
    @0
    @2
    simp33l
    @10
    @7
    vc
    cB
    @11
    wdisj
    @5
    @7
    @3
    @4
    @0
    @2
    simp33r
    vb
    vc
    cB
    @6
    @11
    @6
    @11
    wceq
    #
    id
    cbvdisjv
    sylib
    totprobd
    cB
    @15
    @13
    vb
    vc
    @16
    @14
    @12
    cP
    @6
    @11
    cA
    ineq1
    fveq2d
    cbvesumv
    syl6eqr
end
