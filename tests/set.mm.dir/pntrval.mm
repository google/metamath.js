include "cv.mm"
include "cchp.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "crp.mm"
include "wceq.mm"
include "fveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt.mm"

theorem pntrval
  let cA: class A
  let cR: class R
  let va: setvar a
  let vd: setvar d
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vb: setvar b
  let vc: setvar c
  let vy: setvar y
  assume pntrval.r: |- R = ( a e. RR+ |-> ( ( psi ` a ) - a ) )

  disjoint A a
  disjoint a d
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a x
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint d x
  disjoint A d
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint A m
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint b c
  disjoint b d
  disjoint b k
  disjoint b m
  disjoint b n
  disjoint b x
  disjoint b y
  disjoint R b
  disjoint c d
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c x
  disjoint c y
  disjoint R c
  disjoint d y
  disjoint R d
  disjoint k y
  disjoint R k
  disjoint m y
  disjoint R m
  disjoint n y
  disjoint R n
  disjoint x y
  disjoint R x
  disjoint R y
  assert |- ( A e. RR+ -> ( R ` A ) = ( ( psi ` A ) - A ) )

  proof
    va
    cA
    va
    cv
    #
    cchp
    cfv
    #
    @0
    cmin
    co
    cA
    cchp
    cfv
    #
    cA
    cmin
    co
    crp
    cR
    @0
    cA
    wceq
    #
    @1
    @2
    @0
    cA
    cmin
    @0
    cA
    cchp
    fveq2
    @3
    id
    oveq12d
    pntrval.r
    @2
    cA
    cmin
    ovex
    fvmpt
end
