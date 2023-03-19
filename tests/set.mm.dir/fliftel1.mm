include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "wbr.mm"
include "cmpt.mm"
include "crn.mm"
include "cvv.mm"
include "opex.mm"
include "eqid.mm"
include "elrnmpt1.mm"
include "mpan2.mm"
include "adantl.mm"
include "syl6eleqr.mm"
include "df-br.mm"
include "sylibr.mm"

theorem fliftel1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cY: class Y
  let cD: class D
  assume flift.1: |- F = ran ( x e. X |-> <. A , B >. )
  assume flift.2: |- ( ( ph /\ x e. X ) -> A e. R )
  assume flift.3: |- ( ( ph /\ x e. X ) -> B e. S )

  disjoint R x
  disjoint ph x
  disjoint X x
  disjoint S x
  disjoint u v
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B u
  disjoint B v
  disjoint B y
  disjoint B z
  disjoint u x
  disjoint C u
  disjoint v x
  disjoint C v
  disjoint x z
  disjoint C x
  disjoint C z
  disjoint x y
  disjoint R y
  disjoint R z
  disjoint Y x
  disjoint D u
  disjoint D v
  disjoint D x
  disjoint D z
  disjoint F u
  disjoint F v
  disjoint F y
  disjoint F z
  disjoint ph u
  disjoint ph v
  disjoint ph y
  disjoint ph z
  disjoint X u
  disjoint X v
  disjoint X y
  disjoint X z
  disjoint S y
  disjoint S z
  assert |- ( ( ph /\ x e. X ) -> A F B )

  proof
    wph
    vx
    cv
    cX
    wcel
    #
    wa
    #
    cA
    cB
    cop
    #
    cF
    wcel
    cA
    cB
    cF
    wbr
    @1
    @2
    vx
    cX
    @2
    cmpt
    #
    crn
    #
    cF
    @0
    @2
    @4
    wcel
    #
    wph
    @0
    @2
    cvv
    wcel
    @5
    cA
    cB
    opex
    vx
    cX
    @2
    @3
    cvv
    @3
    eqid
    elrnmpt1
    mpan2
    adantl
    flift.1
    syl6eleqr
    cA
    cB
    cF
    df-br
    sylibr
end
