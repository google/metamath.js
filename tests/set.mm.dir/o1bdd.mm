include "co1.mm"
include "wcel.mm"
include "cc.mm"
include "wf.mm"
include "wa.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cfv.mm"
include "cabs.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "simpl.mm"
include "wss.mm"
include "wb.mm"
include "simpr.mm"
include "cdm.mm"
include "wceq.mm"
include "fdm.mm"
include "adantl.mm"
include "o1dm.mm"
include "adantr.mm"
include "eqsstr3d.mm"
include "elo12.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem o1bdd
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vm: setvar m
  let cF: class F
  let cC: class C
  let vf: setvar f
  let cM: class M

  disjoint m x
  disjoint m y
  disjoint A m
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F m
  disjoint F x
  disjoint F y
  disjoint C m
  disjoint C x
  disjoint C y
  disjoint f m
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint M m
  disjoint M x
  assert |- ( ( F e. O(1) /\ F : A --> CC ) -> E. x e. RR E. m e. RR A. y e. A ( x <_ y -> ( abs ` ( F ` y ) ) <_ m ) )

  proof
    cF
    co1
    wcel
    #
    cA
    cc
    cF
    wf
    #
    wa
    #
    @0
    vx
    cv
    vy
    cv
    #
    cle
    wbr
    @3
    cF
    cfv
    cabs
    cfv
    vm
    cv
    cle
    wbr
    wi
    vy
    cA
    wral
    vm
    cr
    wrex
    vx
    cr
    wrex
    #
    @0
    @1
    simpl
    @2
    @1
    cA
    cr
    wss
    @0
    @4
    wb
    @0
    @1
    simpr
    @2
    cA
    cF
    cdm
    #
    cr
    @1
    @5
    cA
    wceq
    @0
    cA
    cc
    cF
    fdm
    adantl
    @0
    @5
    cr
    wss
    @1
    cF
    o1dm
    adantr
    eqsstr3d
    vx
    vy
    cA
    vm
    cF
    elo12
    syl2anc
    mpbid
end
