include "cop.mm"
include "cxp.mm"
include "cv.mm"
include "wcel.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "cfv.mm"
include "df-ov.mm"
include "eqeq2i.mm"
include "anbi2i.mm"
include "opabbii.mm"
include "eqtri.mm"
include "fnopabco.mm"

theorem opropabco
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cM: class M
  assume opropabco.1: |- ( x e. A -> B e. R )
  assume opropabco.2: |- ( x e. A -> C e. S )
  assume opropabco.3: |- F = { <. x , y >. | ( x e. A /\ y = <. B , C >. ) }
  assume opropabco.4: |- G = { <. x , y >. | ( x e. A /\ y = ( B M C ) ) }

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint C y
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
    #
    cB
    cR
    wcel
    cC
    cS
    wcel
    @0
    @1
    wcel
    opropabco.1
    opropabco.2
    cB
    cC
    cR
    cS
    opelxpi
    syl2anc
    opropabco.3
    cG
    @2
    vy
    cv
    #
    cB
    cC
    cM
    co
    #
    wceq
    #
    wa
    #
    vx
    vy
    copab
    @2
    @3
    @0
    cM
    cfv
    #
    wceq
    #
    wa
    #
    vx
    vy
    copab
    opropabco.4
    @6
    @9
    vx
    vy
    @5
    @8
    @2
    @4
    @7
    @3
    cB
    cC
    cM
    df-ov
    eqeq2i
    anbi2i
    opabbii
    eqtri
    fnopabco
end
