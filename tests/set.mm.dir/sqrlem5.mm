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
include "w3a.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "cc0.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseli.mm"
include "rpge0d.mm"
include "rgen.mm"
include "a1i.mm"
include "sqrlem3.mm"
include "pm4.24.mm"
include "3anbi1i.mm"
include "supmullem2.mm"
include "syl3anc.mm"
include "cmul.mm"
include "sqrlem4.mm"
include "rpre.mm"
include "adantr.mm"
include "syl.mm"
include "recnd.mm"
include "sqvald.mm"
include "oveq12i.mm"
include "supmul.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "jca.mm"

theorem sqrlem5
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let va: setvar a
  let vb: setvar b
  let vz: setvar z
  assume sqrlem1.1: |- S = { x e. RR+ | ( x ^ 2 ) <_ A }
  assume sqrlem1.2: |- B = sup ( S , RR , < )
  assume sqrlem5.3: |- T = { y | E. a e. S E. b e. S y = ( a x. b ) }

  disjoint a b
  disjoint a u
  disjoint a v
  disjoint a y
  disjoint S a
  disjoint b u
  disjoint b v
  disjoint b y
  disjoint S b
  disjoint u v
  disjoint u y
  disjoint S u
  disjoint v y
  disjoint S v
  disjoint S y
  disjoint a x
  disjoint A a
  disjoint b x
  disjoint A b
  disjoint v x
  disjoint A v
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B v
  disjoint B y
  disjoint T u
  disjoint T v
  disjoint a z
  disjoint b z
  disjoint u z
  disjoint v z
  disjoint y z
  disjoint S z
  disjoint x z
  disjoint A z
  disjoint B z
  assert |- ( ( A e. RR+ /\ A <_ 1 ) -> ( ( T C_ RR /\ T =/= (/) /\ E. v e. RR A. u e. T u <_ v ) /\ ( B ^ 2 ) = sup ( T , RR , < ) ) )

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
    cT
    cr
    wss
    cT
    c0
    wne
    vu
    cv
    vv
    cv
    #
    cle
    wbr
    vu
    cT
    wral
    vv
    cr
    wrex
    w3a
    #
    cB
    c2
    cexp
    co
    #
    cT
    cr
    clt
    csup
    #
    wceq
    @0
    cc0
    @1
    cle
    wbr
    #
    vv
    cS
    wral
    #
    cS
    cr
    wss
    cS
    c0
    wne
    vz
    cv
    @1
    cle
    wbr
    vz
    cS
    wral
    vv
    cr
    wrex
    w3a
    #
    @7
    @2
    @6
    @0
    @5
    vv
    cS
    @1
    cS
    wcel
    @1
    cS
    crp
    @1
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
    crp
    sqrlem1.1
    @8
    vx
    crp
    ssrab2
    eqsstri
    sseli
    rpge0d
    rgen
    a1i
    #
    vx
    vz
    vv
    cA
    cB
    cS
    sqrlem1.1
    sqrlem1.2
    sqrlem3
    #
    @10
    @6
    @7
    @7
    w3a
    #
    vv
    vz
    vy
    vu
    va
    cS
    cS
    cT
    vb
    sqrlem5.3
    @6
    @6
    @6
    wa
    @7
    @7
    @6
    pm4.24
    3anbi1i
    #
    supmullem2
    syl3anc
    @0
    @3
    cB
    cB
    cmul
    co
    #
    @4
    @0
    cB
    @0
    cB
    @0
    cB
    crp
    wcel
    #
    cB
    c1
    cle
    wbr
    #
    wa
    cB
    cr
    wcel
    #
    vx
    cA
    cB
    cS
    sqrlem1.1
    sqrlem1.2
    sqrlem4
    @14
    @16
    @15
    cB
    rpre
    adantr
    syl
    recnd
    sqvald
    @0
    @13
    cS
    cr
    clt
    csup
    #
    @17
    cmul
    co
    #
    @4
    cB
    @17
    cB
    @17
    cmul
    sqrlem1.2
    sqrlem1.2
    oveq12i
    @0
    @6
    @7
    @7
    @18
    @4
    wceq
    @9
    @10
    @10
    @11
    vv
    vz
    vy
    va
    cS
    cS
    cT
    vb
    sqrlem5.3
    @12
    supmul
    syl3anc
    syl5eq
    eqtrd
    jca
end
