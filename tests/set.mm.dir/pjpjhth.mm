include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "wa.mm"
include "cpjh.mm"
include "cfv.mm"
include "cort.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "wrex.mm"
include "axpjcl.mm"
include "choccl.mm"
include "sylan.mm"
include "axpjpj.mm"
include "rspceov.mm"
include "syl3anc.mm"

theorem pjpjhth
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cH: class H

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint H x
  disjoint H y
  assert |- ( ( H e. CH /\ A e. ~H ) -> E. x e. H E. y e. ( _|_ ` H ) A = ( x +h y ) )

  proof
    cH
    cch
    wcel
    #
    cA
    chil
    wcel
    #
    wa
    cA
    cH
    cpjh
    cfv
    cfv
    #
    cH
    wcel
    cA
    cH
    cort
    cfv
    #
    cpjh
    cfv
    cfv
    #
    @3
    wcel
    #
    cA
    @2
    @4
    cva
    co
    wceq
    cA
    vx
    cv
    vy
    cv
    cva
    co
    wceq
    vy
    @3
    wrex
    vx
    cH
    wrex
    cA
    cH
    axpjcl
    @0
    @3
    cch
    wcel
    @1
    @5
    cH
    choccl
    cA
    @3
    axpjcl
    sylan
    cA
    cH
    axpjpj
    vx
    vy
    cH
    @3
    @2
    @4
    cA
    cva
    rspceov
    syl3anc
end
