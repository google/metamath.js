include "cop.mm"
include "cxp.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "co.mm"
include "cmpt2.mm"
include "cfv.mm"
include "wceq.mm"
include "df-ov.mm"
include "a1i.mm"
include "mpt2eq3ia.mm"
include "eqtri.mm"
include "oprabco.mm"

theorem oprab2co
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cM: class M
  assume oprab2co.1: |- ( ( x e. A /\ y e. B ) -> C e. R )
  assume oprab2co.2: |- ( ( x e. A /\ y e. B ) -> D e. S )
  assume oprab2co.3: |- F = ( x e. A , y e. B |-> <. C , D >. )
  assume oprab2co.4: |- G = ( x e. A , y e. B |-> ( C M D ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint M x
  disjoint M y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  assert |- ( M Fn ( R X. S ) -> G = ( M o. F ) )

  proof
    vx
    vy
    cA
    cB
    cC
    cD
    cop
    #
    cR
    cS
    cxp
    #
    cF
    cG
    cM
    vx
    cv
    cA
    wcel
    vy
    cv
    cB
    wcel
    wa
    #
    cC
    cR
    wcel
    cD
    cS
    wcel
    @0
    @1
    wcel
    oprab2co.1
    oprab2co.2
    cC
    cD
    cR
    cS
    opelxpi
    syl2anc
    oprab2co.3
    cG
    vx
    vy
    cA
    cB
    cC
    cD
    cM
    co
    #
    cmpt2
    vx
    vy
    cA
    cB
    @0
    cM
    cfv
    #
    cmpt2
    oprab2co.4
    vx
    vy
    cA
    cB
    @3
    @4
    @3
    @4
    wceq
    @2
    cC
    cD
    cM
    df-ov
    a1i
    mpt2eq3ia
    eqtri
    oprabco
end
