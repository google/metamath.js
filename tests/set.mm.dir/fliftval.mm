include "wcel.mm"
include "wa.mm"
include "wfun.mm"
include "wbr.mm"
include "cfv.mm"
include "wceq.mm"
include "adantr.mm"
include "wrex.mm"
include "simpr.mm"
include "eqidd.mm"
include "anim12ci.mm"
include "cv.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wb.mm"
include "fliftel.mm"
include "mpbird.mm"
include "funbrfv.mm"
include "sylc.mm"

theorem fliftval
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
  let cY: class Y
  let vu: setvar u
  let vv: setvar v
  let vy: setvar y
  let vz: setvar z
  assume flift.1: |- F = ran ( x e. X |-> <. A , B >. )
  assume flift.2: |- ( ( ph /\ x e. X ) -> A e. R )
  assume flift.3: |- ( ( ph /\ x e. X ) -> B e. S )
  assume fliftval.4: |- ( x = Y -> A = C )
  assume fliftval.5: |- ( x = Y -> B = D )
  assume fliftval.6: |- ( ph -> Fun F )

  disjoint C x
  disjoint R x
  disjoint Y x
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
  assert |- ( ( ph /\ Y e. X ) -> ( F ` C ) = D )

  proof
    wph
    cY
    cX
    wcel
    #
    wa
    #
    cF
    wfun
    #
    cC
    cD
    cF
    wbr
    #
    cC
    cF
    cfv
    cD
    wceq
    wph
    @2
    @0
    fliftval.6
    adantr
    @1
    @3
    cC
    cA
    wceq
    #
    cD
    cB
    wceq
    #
    wa
    #
    vx
    cX
    wrex
    #
    @1
    @0
    cC
    cC
    wceq
    #
    cD
    cD
    wceq
    #
    wa
    #
    @7
    wph
    @0
    simpr
    wph
    @9
    @0
    @8
    wph
    cD
    eqidd
    @0
    cC
    eqidd
    anim12ci
    @6
    @10
    vx
    cY
    cX
    vx
    cv
    cY
    wceq
    #
    @4
    @8
    @5
    @9
    @11
    cA
    cC
    cC
    fliftval.4
    eqeq2d
    @11
    cB
    cD
    cD
    fliftval.5
    eqeq2d
    anbi12d
    rspcev
    syl2anc
    wph
    @3
    @7
    wb
    @0
    wph
    vx
    cA
    cB
    cC
    cD
    cR
    cS
    cF
    cX
    flift.1
    flift.2
    flift.3
    fliftel
    adantr
    mpbird
    cC
    cD
    cF
    funbrfv
    sylc
end
