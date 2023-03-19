include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wral.mm"
include "wrex.mm"
include "w3a.mm"
include "sqrlem3.mm"
include "suprcl.mm"
include "syl.mm"
include "syl5eqel.mm"
include "cc0.mm"
include "rpgt0.mm"
include "adantr.mm"
include "sqrlem2.mm"
include "suprub.mm"
include "syl2anc.mm"
include "syl6breqr.mm"
include "wi.mm"
include "rpre.mm"
include "0re.mm"
include "ltletr.mm"
include "mp3an1.mm"
include "mp2and.mm"
include "elrpd.mm"
include "sqrlem1.mm"
include "wb.mm"
include "1re.mm"
include "suprleub.mm"
include "sylancl.mm"
include "mpbird.mm"
include "syl5eqbr.mm"
include "jca.mm"

theorem sqrlem4
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S
  let va: setvar a
  let vb: setvar b
  let vu: setvar u
  let vv: setvar v
  let vy: setvar y
  let vz: setvar z
  assume sqrlem1.1: |- S = { x e. RR+ | ( x ^ 2 ) <_ A }
  assume sqrlem1.2: |- B = sup ( S , RR , < )

  disjoint A x
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
  disjoint y z
  disjoint S y
  disjoint S z
  disjoint a x
  disjoint A a
  disjoint b x
  disjoint A b
  disjoint v x
  disjoint A v
  disjoint x y
  disjoint x z
  disjoint A y
  disjoint A z
  disjoint B v
  disjoint B y
  disjoint B z
  assert |- ( ( A e. RR+ /\ A <_ 1 ) -> ( B e. RR+ /\ B <_ 1 ) )

  proof
    cA
    crp
    wcel
    #
    cA
    c1
    cle
    wbr
    #
    wa
    #
    cB
    crp
    wcel
    cB
    c1
    cle
    wbr
    @2
    cB
    @2
    cB
    cS
    cr
    clt
    csup
    #
    cr
    sqrlem1.2
    @2
    cS
    cr
    wss
    cS
    c0
    wne
    vz
    cv
    #
    vy
    cv
    cle
    wbr
    vz
    cS
    wral
    vy
    cr
    wrex
    w3a
    #
    @3
    cr
    wcel
    vx
    vz
    vy
    cA
    cB
    cS
    sqrlem1.1
    sqrlem1.2
    sqrlem3
    #
    vy
    vz
    cS
    suprcl
    syl
    syl5eqel
    #
    @2
    cc0
    cA
    clt
    wbr
    #
    cA
    cB
    cle
    wbr
    #
    cc0
    cB
    clt
    wbr
    #
    @0
    @8
    @1
    cA
    rpgt0
    adantr
    @2
    cA
    @3
    cB
    cle
    @2
    @5
    cA
    cS
    wcel
    cA
    @3
    cle
    wbr
    @6
    vx
    cA
    cB
    cS
    sqrlem1.1
    sqrlem1.2
    sqrlem2
    vy
    vz
    cS
    cA
    suprub
    syl2anc
    sqrlem1.2
    syl6breqr
    @2
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @8
    @9
    wa
    @10
    wi
    #
    @0
    @11
    @1
    cA
    rpre
    adantr
    @7
    cc0
    cr
    wcel
    @11
    @12
    @13
    0re
    cc0
    cA
    cB
    ltletr
    mp3an1
    syl2anc
    mp2and
    elrpd
    @2
    cB
    @3
    c1
    cle
    sqrlem1.2
    @2
    @3
    c1
    cle
    wbr
    #
    @4
    c1
    cle
    wbr
    vz
    cS
    wral
    #
    vx
    vz
    cA
    cB
    cS
    sqrlem1.1
    sqrlem1.2
    sqrlem1
    @2
    @5
    c1
    cr
    wcel
    @14
    @15
    wb
    @6
    1re
    vy
    vz
    vz
    cS
    c1
    suprleub
    sylancl
    mpbird
    syl5eqbr
    jca
end
