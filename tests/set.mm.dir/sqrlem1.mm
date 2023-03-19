include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "weq.mm"
include "oveq1.mm"
include "breq1d.mm"
include "elrab2.mm"
include "simprr.mm"
include "simplr.mm"
include "cr.mm"
include "wi.mm"
include "rpre.mm"
include "ad2antrl.mm"
include "resqcld.mm"
include "ad2antrr.mm"
include "1re.mm"
include "letr.mm"
include "mp3an3.mm"
include "syl2anc.mm"
include "mp2and.mm"
include "sq1.mm"
include "syl6breqr.mm"
include "cc0.mm"
include "wb.mm"
include "rpge0.mm"
include "0le1.mm"
include "le2sq.mm"
include "mpanr12.mm"
include "mpbird.mm"
include "ex.mm"
include "syl5bi.mm"
include "ralrimiv.mm"

theorem sqrlem1
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cS: class S
  let va: setvar a
  let vb: setvar b
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  assume sqrlem1.1: |- S = { x e. RR+ | ( x ^ 2 ) <_ A }
  assume sqrlem1.2: |- B = sup ( S , RR , < )

  disjoint S y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
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
  disjoint S z
  disjoint a x
  disjoint A a
  disjoint b x
  disjoint A b
  disjoint v x
  disjoint A v
  disjoint x z
  disjoint A z
  disjoint B v
  disjoint B z
  assert |- ( ( A e. RR+ /\ A <_ 1 ) -> A. y e. S y <_ 1 )

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
    vy
    cv
    #
    c1
    cle
    wbr
    #
    vy
    cS
    @3
    cS
    wcel
    @3
    crp
    wcel
    #
    @3
    c2
    cexp
    co
    #
    cA
    cle
    wbr
    #
    wa
    #
    @2
    @4
    vx
    cv
    #
    c2
    cexp
    co
    #
    cA
    cle
    wbr
    @7
    vx
    @3
    crp
    cS
    vx
    vy
    weq
    @10
    @6
    cA
    cle
    @9
    @3
    c2
    cexp
    oveq1
    breq1d
    sqrlem1.1
    elrab2
    @2
    @8
    @4
    @2
    @8
    wa
    #
    @4
    @6
    c1
    c2
    cexp
    co
    #
    cle
    wbr
    #
    @11
    @6
    c1
    @12
    cle
    @11
    @7
    @1
    @6
    c1
    cle
    wbr
    #
    @2
    @5
    @7
    simprr
    @0
    @1
    @8
    simplr
    @11
    @6
    cr
    wcel
    #
    cA
    cr
    wcel
    #
    @7
    @1
    wa
    @14
    wi
    #
    @11
    @3
    @5
    @3
    cr
    wcel
    #
    @2
    @7
    @3
    rpre
    ad2antrl
    #
    resqcld
    @0
    @16
    @1
    @8
    cA
    rpre
    ad2antrr
    @15
    @16
    c1
    cr
    wcel
    #
    @17
    1re
    @6
    cA
    c1
    letr
    mp3an3
    syl2anc
    mp2and
    sq1
    syl6breqr
    @11
    @18
    cc0
    @3
    cle
    wbr
    #
    @4
    @13
    wb
    #
    @19
    @5
    @21
    @2
    @7
    @3
    rpge0
    ad2antrl
    @18
    @21
    wa
    @20
    cc0
    c1
    cle
    wbr
    @22
    1re
    0le1
    @3
    c1
    le2sq
    mpanr12
    syl2anc
    mpbird
    ex
    syl5bi
    ralrimiv
end
