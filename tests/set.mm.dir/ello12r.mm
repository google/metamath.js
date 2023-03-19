include "cr.mm"
include "wf.mm"
include "wss.mm"
include "wa.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "w3a.mm"
include "clo1.mm"
include "wrex.mm"
include "wceq.mm"
include "breq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "breq2.mm"
include "imbi2d.mm"
include "rspc2ev.mm"
include "3expa.mm"
include "3adant1.mm"
include "wb.mm"
include "ello12.mm"
include "3ad2ant1.mm"
include "mpbird.mm"

theorem ello12r
  let vx: setvar x
  let cA: class A
  let cC: class C
  let cF: class F
  let cM: class M
  let vm: setvar m
  let vy: setvar y
  let vf: setvar f

  disjoint A x
  disjoint C x
  disjoint F x
  disjoint M x
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint x y
  disjoint A y
  disjoint C m
  disjoint C y
  disjoint f m
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint F m
  disjoint F y
  disjoint M m
  assert |- ( ( ( F : A --> RR /\ A C_ RR ) /\ ( C e. RR /\ M e. RR ) /\ A. x e. A ( C <_ x -> ( F ` x ) <_ M ) ) -> F e. <_O(1) )

  proof
    cA
    cr
    cF
    wf
    cA
    cr
    wss
    wa
    #
    cC
    cr
    wcel
    #
    cM
    cr
    wcel
    #
    wa
    #
    cC
    vx
    cv
    #
    cle
    wbr
    #
    @4
    cF
    cfv
    #
    cM
    cle
    wbr
    #
    wi
    #
    vx
    cA
    wral
    #
    w3a
    cF
    clo1
    wcel
    #
    vy
    cv
    #
    @4
    cle
    wbr
    #
    @6
    vm
    cv
    #
    cle
    wbr
    #
    wi
    #
    vx
    cA
    wral
    #
    vm
    cr
    wrex
    vy
    cr
    wrex
    #
    @3
    @9
    @17
    @0
    @1
    @2
    @9
    @17
    @16
    @9
    @5
    @14
    wi
    #
    vx
    cA
    wral
    vy
    vm
    cC
    cM
    cr
    cr
    @11
    cC
    wceq
    #
    @15
    @18
    vx
    cA
    @19
    @12
    @5
    @14
    @11
    cC
    @4
    cle
    breq1
    imbi1d
    ralbidv
    @13
    cM
    wceq
    #
    @18
    @8
    vx
    cA
    @20
    @14
    @7
    @5
    @13
    cM
    @6
    cle
    breq2
    imbi2d
    ralbidv
    rspc2ev
    3expa
    3adant1
    @0
    @3
    @10
    @17
    wb
    @9
    vy
    vx
    cA
    vm
    cF
    ello12
    3ad2ant1
    mpbird
end
