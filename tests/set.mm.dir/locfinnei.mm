include "clocfin.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "crab.mm"
include "cfn.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "ctop.mm"
include "cuni.mm"
include "wceq.mm"
include "eqid.mm"
include "islocfin.mm"
include "simp3bi.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "rspccva.mm"
include "sylan.mm"

theorem locfinnei
  let cA: class A
  let cP: class P
  let vn: setvar n
  let cJ: class J
  let cX: class X
  let vs: setvar s
  let vx: setvar x
  assume locfinnei.1: |- X = U. J

  disjoint n s
  disjoint A n
  disjoint A s
  disjoint J n
  disjoint P n
  disjoint n x
  disjoint s x
  disjoint A x
  disjoint J x
  disjoint P x
  disjoint X x
  assert |- ( ( A e. ( LocFin ` J ) /\ P e. X ) -> E. n e. J ( P e. n /\ { s e. A | ( s i^i n ) =/= (/) } e. Fin ) )

  proof
    cA
    cJ
    clocfin
    cfv
    wcel
    #
    vx
    cv
    #
    vn
    cv
    #
    wcel
    #
    vs
    cv
    @2
    cin
    c0
    wne
    vs
    cA
    crab
    cfn
    wcel
    #
    wa
    #
    vn
    cJ
    wrex
    #
    vx
    cX
    wral
    #
    cP
    cX
    wcel
    cP
    @2
    wcel
    #
    @4
    wa
    #
    vn
    cJ
    wrex
    #
    @0
    cJ
    ctop
    wcel
    cX
    cA
    cuni
    #
    wceq
    @7
    vx
    cA
    vn
    cJ
    cX
    @11
    vs
    locfinnei.1
    @11
    eqid
    islocfin
    simp3bi
    @6
    @10
    vx
    cP
    cX
    @1
    cP
    wceq
    #
    @5
    @9
    vn
    cJ
    @12
    @3
    @8
    @4
    @1
    cP
    @2
    eleq1
    anbi1d
    rexbidv
    rspccva
    sylan
end
