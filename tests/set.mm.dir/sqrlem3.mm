include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wral.mm"
include "wrex.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "crab.mm"
include "ssrab2.mm"
include "rpssre.mm"
include "sstri.mm"
include "eqsstri.mm"
include "a1i.mm"
include "sqrlem2.mm"
include "ne0i.mm"
include "syl.mm"
include "1re.mm"
include "sqrlem1.mm"
include "wceq.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "sylancr.mm"
include "3jca.mm"

theorem sqrlem3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cS: class S
  let va: setvar a
  let vb: setvar b
  let vu: setvar u
  let vv: setvar v
  assume sqrlem1.1: |- S = { x e. RR+ | ( x ^ 2 ) <_ A }
  assume sqrlem1.2: |- B = sup ( S , RR , < )

  disjoint y z
  disjoint S y
  disjoint S z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint a b
  disjoint a u
  disjoint a v
  disjoint a y
  disjoint a z
  disjoint S a
  disjoint b u
  disjoint b v
  disjoint b y
  disjoint b z
  disjoint S b
  disjoint u v
  disjoint u y
  disjoint u z
  disjoint S u
  disjoint v y
  disjoint v z
  disjoint S v
  disjoint a x
  disjoint A a
  disjoint b x
  disjoint A b
  disjoint v x
  disjoint A v
  disjoint B v
  assert |- ( ( A e. RR+ /\ A <_ 1 ) -> ( S C_ RR /\ S =/= (/) /\ E. z e. RR A. y e. S y <_ z ) )

  proof
    cA
    crp
    wcel
    cA
    c1
    cle
    wbr
    wa
    #
    cS
    cr
    wss
    #
    cS
    c0
    wne
    #
    vy
    cv
    #
    vz
    cv
    #
    cle
    wbr
    #
    vy
    cS
    wral
    #
    vz
    cr
    wrex
    #
    @1
    @0
    cS
    vx
    cv
    c2
    cexp
    co
    cA
    cle
    wbr
    #
    vx
    crp
    crab
    #
    cr
    sqrlem1.1
    @9
    crp
    cr
    @8
    vx
    crp
    ssrab2
    rpssre
    sstri
    eqsstri
    a1i
    @0
    cA
    cS
    wcel
    @2
    vx
    cA
    cB
    cS
    sqrlem1.1
    sqrlem1.2
    sqrlem2
    cS
    cA
    ne0i
    syl
    @0
    c1
    cr
    wcel
    @3
    c1
    cle
    wbr
    #
    vy
    cS
    wral
    #
    @7
    1re
    vx
    vy
    cA
    cB
    cS
    sqrlem1.1
    sqrlem1.2
    sqrlem1
    @6
    @11
    vz
    c1
    cr
    @4
    c1
    wceq
    @5
    @10
    vy
    cS
    @4
    c1
    @3
    cle
    breq2
    ralbidv
    rspcev
    sylancr
    3jca
end
