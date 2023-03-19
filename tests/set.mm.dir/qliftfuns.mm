include "cv.mm"
include "csb.mm"
include "cec.mm"
include "cop.mm"
include "cmpt.mm"
include "crn.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfop.mm"
include "weq.mm"
include "eceq1.mm"
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
include "qliftfun.mm"

theorem qliftfuns
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R
  let cF: class F
  let cX: class X
  let cY: class Y
  let cB: class B
  let cC: class C
  let cD: class D
  assume qlift.1: |- F = ran ( x e. X |-> <. [ x ] R , A >. )
  assume qlift.2: |- ( ( ph /\ x e. X ) -> A e. Y )
  assume qlift.3: |- ( ph -> R Er X )
  assume qlift.4: |- ( ph -> X e. _V )

  disjoint y z
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint F y
  disjoint F z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint B x
  disjoint C x
  disjoint D x
  assert |- ( ph -> ( Fun F <-> A. y A. z ( y R z -> [_ y / x ]_ A = [_ z / x ]_ A ) ) )

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
    vz
    cv
    #
    cA
    csb
    cR
    cF
    cX
    cY
    cF
    vx
    cX
    vx
    cv
    #
    cR
    cec
    #
    cA
    cop
    #
    cmpt
    #
    crn
    vy
    cX
    @0
    cR
    cec
    #
    @1
    cop
    #
    cmpt
    #
    crn
    qlift.1
    @6
    @9
    vx
    vy
    cX
    @5
    @8
    vy
    @5
    nfcv
    vx
    @7
    @1
    vx
    @7
    nfcv
    vx
    @0
    cA
    nfcsb1v
    #
    nfop
    vx
    vy
    weq
    #
    @4
    @7
    cA
    @1
    @3
    @0
    cR
    eceq1
    vx
    @0
    cA
    csbeq1a
    #
    opeq12d
    cbvmpt
    rneqi
    eqtri
    wph
    cA
    cY
    wcel
    #
    vx
    cX
    wral
    @0
    cX
    wcel
    @1
    cY
    wcel
    #
    wph
    @13
    vx
    cX
    qlift.2
    ralrimiva
    @13
    @14
    vx
    @0
    cX
    vx
    @1
    cY
    @10
    nfel1
    @11
    cA
    @1
    cY
    @12
    eleq1d
    rspc
    mpan9
    qlift.3
    qlift.4
    vx
    @0
    @2
    cA
    csbeq1
    qliftfun
end
