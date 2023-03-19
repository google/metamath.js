include "cii.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "iitopon.mm"
include "a1i.mm"
include "htpyid.mm"
include "cv.mm"
include "wceq.mm"
include "0elunit.mm"
include "fveq2.mm"
include "eqidd.mm"
include "fvex.mm"
include "ovmpt2.mm"
include "mpan.mm"
include "adantl.mm"
include "1elunit.mm"
include "isphtpyd.mm"

theorem phtpyid
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cG: class G
  let cJ: class J
  let vs: setvar s
  assume phtpyid.1: |- G = ( x e. ( 0 [,] 1 ) , y e. ( 0 [,] 1 ) |-> ( F ` x ) )
  assume phtpyid.3: |- ( ph -> F e. ( II Cn J ) )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint J x
  disjoint J y
  disjoint ph x
  disjoint ph y
  disjoint s x
  disjoint s y
  disjoint F s
  disjoint G s
  disjoint J s
  disjoint ph s
  assert |- ( ph -> G e. ( F ( PHtpy ` J ) F ) )

  proof
    wph
    cF
    cF
    cG
    cJ
    vs
    phtpyid.3
    phtpyid.3
    wph
    vx
    vy
    cF
    cG
    cii
    cJ
    cc0
    c1
    cicc
    co
    #
    phtpyid.1
    cii
    @0
    ctopon
    cfv
    wcel
    wph
    iitopon
    a1i
    phtpyid.3
    htpyid
    vs
    cv
    #
    @0
    wcel
    #
    cc0
    @1
    cG
    co
    cc0
    cF
    cfv
    #
    wceq
    #
    wph
    cc0
    @0
    wcel
    @2
    @4
    0elunit
    vx
    vy
    cc0
    @1
    @0
    @0
    vx
    cv
    #
    cF
    cfv
    #
    @3
    cG
    @3
    @5
    cc0
    cF
    fveq2
    vy
    cv
    @1
    wceq
    #
    @3
    eqidd
    phtpyid.1
    cc0
    cF
    fvex
    ovmpt2
    mpan
    adantl
    @2
    c1
    @1
    cG
    co
    c1
    cF
    cfv
    #
    wceq
    #
    wph
    c1
    @0
    wcel
    @2
    @9
    1elunit
    vx
    vy
    c1
    @1
    @0
    @0
    @6
    @8
    cG
    @8
    @5
    c1
    cF
    fveq2
    @7
    @8
    eqidd
    phtpyid.1
    c1
    cF
    fvex
    ovmpt2
    mpan
    adantl
    isphtpyd
end
