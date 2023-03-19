include "cop.mm"
include "cmpt.mm"
include "crn.mm"
include "cxp.mm"
include "wf.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "syl.mm"
include "syl5eqss.mm"

theorem fliftrel
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
  assert |- ( ph -> F C_ ( R X. S ) )

  proof
    wph
    cF
    vx
    cX
    cA
    cB
    cop
    #
    cmpt
    #
    crn
    #
    cR
    cS
    cxp
    #
    flift.1
    wph
    cX
    @3
    @1
    wf
    @2
    @3
    wss
    wph
    vx
    cX
    @0
    @3
    @1
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
    @0
    @3
    wcel
    flift.2
    flift.3
    cA
    cB
    cR
    cS
    opelxpi
    syl2anc
    @1
    eqid
    fmptd
    cX
    @3
    @1
    frn
    syl
    syl5eqss
end
