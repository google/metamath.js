include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "cre.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "ci.mm"
include "cmul.mm"
include "crp.mm"
include "wnel.mm"
include "w3a.mm"
include "cc.mm"
include "crio.mm"
include "csqrt.mm"
include "eqeq2.mm"
include "3anbi1d.mm"
include "riotabidv.mm"
include "df-sqrt.mm"
include "riotaex.mm"
include "fvmpt.mm"

theorem sqrtval
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( A e. CC -> ( sqrt ` A ) = ( iota_ x e. CC ( ( x ^ 2 ) = A /\ 0 <_ ( Re ` x ) /\ ( _i x. x ) e/ RR+ ) ) )

  proof
    vy
    cA
    vx
    cv
    #
    c2
    cexp
    co
    #
    vy
    cv
    #
    wceq
    #
    cc0
    @0
    cre
    cfv
    cle
    wbr
    #
    ci
    @0
    cmul
    co
    crp
    wnel
    #
    w3a
    #
    vx
    cc
    crio
    @1
    cA
    wceq
    #
    @4
    @5
    w3a
    #
    vx
    cc
    crio
    cc
    csqrt
    @2
    cA
    wceq
    #
    @6
    @8
    vx
    cc
    @9
    @3
    @7
    @4
    @5
    @2
    cA
    @1
    eqeq2
    3anbi1d
    riotabidv
    vy
    vx
    df-sqrt
    @8
    vx
    cc
    riotaex
    fvmpt
end
