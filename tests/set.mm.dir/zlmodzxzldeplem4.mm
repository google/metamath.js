include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "cpr.mm"
include "wrex.mm"
include "c3.mm"
include "cop.mm"
include "c1.mm"
include "c6.mm"
include "prex.mm"
include "eqeltri.mm"
include "c2.mm"
include "c4.mm"
include "wa.mm"
include "wo.mm"
include "2ne0.mm"
include "cneg.mm"
include "fveq1i.mm"
include "wceq.mm"
include "zlmodzxzldeplem.mm"
include "2ex.mm"
include "fvpr1.mm"
include "mp1i.mm"
include "syl5eq.mm"
include "neeq1d.mm"
include "mpbiri.mm"
include "orcd.mm"
include "fveq2.mm"
include "rexprg.mm"
include "mpbird.mm"
include "mp2an.mm"

theorem zlmodzxzldeplem4
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cZ: class Z
  let vx: setvar x
  let vk: setvar k
  assume zlmodzxzldep.z: |- Z = ( ZZring freeLMod { 0 , 1 } )
  assume zlmodzxzldep.a: |- A = { <. 0 , 3 >. , <. 1 , 6 >. }
  assume zlmodzxzldep.b: |- B = { <. 0 , 2 >. , <. 1 , 4 >. }
  assume zlmodzxzldeplem.f: |- F = { <. A , 2 >. , <. B , -u 3 >. }

  disjoint A y
  disjoint B y
  disjoint F y
  disjoint A x
  disjoint B x
  disjoint F x
  disjoint Z x
  disjoint k x
  assert |- E. y e. { A , B } ( F ` y ) =/= 0

  proof
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    vy
    cv
    #
    cF
    cfv
    #
    cc0
    wne
    #
    vy
    cA
    cB
    cpr
    wrex
    #
    cA
    cc0
    c3
    cop
    #
    c1
    c6
    cop
    #
    cpr
    cvv
    zlmodzxzldep.a
    @6
    @7
    prex
    eqeltri
    #
    cB
    cc0
    c2
    cop
    #
    c1
    c4
    cop
    #
    cpr
    cvv
    zlmodzxzldep.b
    @9
    @10
    prex
    eqeltri
    @0
    @1
    wa
    #
    @5
    cA
    cF
    cfv
    #
    cc0
    wne
    #
    cB
    cF
    cfv
    #
    cc0
    wne
    #
    wo
    @11
    @13
    @15
    @11
    @13
    c2
    cc0
    wne
    2ne0
    @11
    @12
    c2
    cc0
    @11
    @12
    cA
    cA
    c2
    cop
    cB
    c3
    cneg
    #
    cop
    cpr
    #
    cfv
    #
    c2
    cA
    cF
    @17
    zlmodzxzldeplem.f
    fveq1i
    cA
    cB
    wne
    @18
    c2
    wceq
    @11
    cA
    cB
    cZ
    zlmodzxzldep.z
    zlmodzxzldep.a
    zlmodzxzldep.b
    zlmodzxzldeplem
    cA
    cB
    c2
    @16
    @8
    2ex
    fvpr1
    mp1i
    syl5eq
    neeq1d
    mpbiri
    orcd
    @4
    @13
    @15
    vy
    cA
    cB
    cvv
    cvv
    @2
    cA
    wceq
    @3
    @12
    cc0
    @2
    cA
    cF
    fveq2
    neeq1d
    @2
    cB
    wceq
    @3
    @14
    cc0
    @2
    cB
    cF
    fveq2
    neeq1d
    rexprg
    mpbird
    mp2an
end
