include "wbr.mm"
include "cop.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "wcel.mm"
include "cmpt.mm"
include "crn.mm"
include "df-br.mm"
include "eleq2i.mm"
include "eqid.mm"
include "opex.mm"
include "elrnmpti.mm"
include "3bitri.mm"
include "cv.mm"
include "wb.mm"
include "opthg2.mm"
include "syl2anc.mm"
include "rexbidva.mm"
include "syl5bb.mm"

theorem fliftel
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cF: class F
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let vy: setvar y
  let vz: setvar z
  let cY: class Y
  assume flift.1: |- F = ran ( x e. X |-> <. A , B >. )
  assume flift.2: |- ( ( ph /\ x e. X ) -> A e. R )
  assume flift.3: |- ( ( ph /\ x e. X ) -> B e. S )

  disjoint C x
  disjoint R x
  disjoint D x
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
  disjoint C z
  disjoint x y
  disjoint R y
  disjoint R z
  disjoint Y x
  disjoint D u
  disjoint D v
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
  assert |- ( ph -> ( C F D <-> E. x e. X ( C = A /\ D = B ) ) )

  proof
    cC
    cD
    cF
    wbr
    #
    cC
    cD
    cop
    #
    cA
    cB
    cop
    #
    wceq
    #
    vx
    cX
    wrex
    #
    wph
    cC
    cA
    wceq
    cD
    cB
    wceq
    wa
    #
    vx
    cX
    wrex
    @0
    @1
    cF
    wcel
    @1
    vx
    cX
    @2
    cmpt
    #
    crn
    #
    wcel
    @4
    cC
    cD
    cF
    df-br
    cF
    @7
    @1
    flift.1
    eleq2i
    vx
    cX
    @2
    @1
    @6
    @6
    eqid
    cA
    cB
    opex
    elrnmpti
    3bitri
    wph
    @3
    @5
    vx
    cX
    wph
    vx
    cv
    cX
    wcel
    wa
    cA
    cR
    wcel
    cB
    cS
    wcel
    @3
    @5
    wb
    flift.2
    flift.3
    cC
    cD
    cA
    cB
    cR
    cS
    opthg2
    syl2anc
    rexbidva
    syl5bb
end
