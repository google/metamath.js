include "cv.mm"
include "csb.mm"
include "cop.mm"
include "cmpt.mm"
include "crn.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfop.mm"
include "weq.mm"
include "csbeq1a.mm"
include "opeq12d.mm"
include "cbvmpt.mm"
include "rneqi.mm"
include "eqtri.mm"
include "wcel.mm"
include "wral.mm"
include "ralrimiva.mm"
include "nfel1.mm"
include "eleq1d.mm"
include "rspc.mm"
include "mpan9.mm"
include "csbeq1.mm"
include "fliftfun.mm"

theorem fliftfuns
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let cC: class C
  let cY: class Y
  let cD: class D
  assume flift.1: |- F = ran ( x e. X |-> <. A , B >. )
  assume flift.2: |- ( ( ph /\ x e. X ) -> A e. R )
  assume flift.3: |- ( ( ph /\ x e. X ) -> B e. S )

  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint x z
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint F y
  disjoint F z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint u v
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint B u
  disjoint B v
  disjoint u x
  disjoint C u
  disjoint v x
  disjoint C v
  disjoint C x
  disjoint C z
  disjoint Y x
  disjoint D u
  disjoint D v
  disjoint D x
  disjoint D z
  disjoint F u
  disjoint F v
  disjoint ph u
  disjoint ph v
  disjoint X u
  disjoint X v
  assert |- ( ph -> ( Fun F <-> A. y e. X A. z e. X ( [_ y / x ]_ A = [_ z / x ]_ A -> [_ y / x ]_ B = [_ z / x ]_ B ) ) )

  proof
    wph
    vy
    vz
    vx
    vy
    cv
    #
    cA
    csb
    #
    vx
    @0
    cB
    csb
    #
    vx
    vz
    cv
    #
    cA
    csb
    vx
    @3
    cB
    csb
    cR
    cS
    cF
    cX
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
    vy
    cX
    @1
    @2
    cop
    #
    cmpt
    #
    crn
    flift.1
    @5
    @7
    vx
    vy
    cX
    @4
    @6
    vy
    @4
    nfcv
    vx
    @1
    @2
    vx
    @0
    cA
    nfcsb1v
    #
    vx
    @0
    cB
    nfcsb1v
    #
    nfop
    vx
    vy
    weq
    #
    cA
    @1
    cB
    @2
    vx
    @0
    cA
    csbeq1a
    #
    vx
    @0
    cB
    csbeq1a
    #
    opeq12d
    cbvmpt
    rneqi
    eqtri
    wph
    cA
    cR
    wcel
    #
    vx
    cX
    wral
    @0
    cX
    wcel
    #
    @1
    cR
    wcel
    #
    wph
    @13
    vx
    cX
    flift.2
    ralrimiva
    @13
    @15
    vx
    @0
    cX
    vx
    @1
    cR
    @8
    nfel1
    @10
    cA
    @1
    cR
    @11
    eleq1d
    rspc
    mpan9
    wph
    cB
    cS
    wcel
    #
    vx
    cX
    wral
    @14
    @2
    cS
    wcel
    #
    wph
    @16
    vx
    cX
    flift.3
    ralrimiva
    @16
    @17
    vx
    @0
    cX
    vx
    @2
    cS
    @9
    nfel1
    @10
    cB
    @2
    cS
    @12
    eleq1d
    rspc
    mpan9
    vx
    @0
    @3
    cA
    csbeq1
    vx
    @0
    @3
    cB
    csbeq1
    fliftfun
end
