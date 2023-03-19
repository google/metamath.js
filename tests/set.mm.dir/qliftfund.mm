include "wfun.mm"
include "cv.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "ex.mm"
include "alrimivv.mm"
include "qliftfun.mm"
include "mpbird.mm"

theorem qliftfund
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cX: class X
  let cY: class Y
  let vz: setvar z
  let cC: class C
  let cD: class D
  assume qlift.1: |- F = ran ( x e. X |-> <. [ x ] R , A >. )
  assume qlift.2: |- ( ( ph /\ x e. X ) -> A e. Y )
  assume qlift.3: |- ( ph -> R Er X )
  assume qlift.4: |- ( ph -> X e. _V )
  assume qliftfun.4: |- ( x = y -> A = B )
  assume qliftfund.6: |- ( ( ph /\ x R y ) -> A = B )

  disjoint A y
  disjoint B x
  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint R x
  disjoint R y
  disjoint F y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint y z
  disjoint A z
  disjoint C x
  disjoint D x
  disjoint x z
  disjoint ph z
  disjoint R z
  disjoint F z
  disjoint X z
  disjoint Y z
  assert |- ( ph -> Fun F )

  proof
    wph
    cF
    wfun
    vx
    cv
    vy
    cv
    cR
    wbr
    #
    cA
    cB
    wceq
    #
    wi
    #
    vy
    wal
    vx
    wal
    wph
    @2
    vx
    vy
    wph
    @0
    @1
    qliftfund.6
    ex
    alrimivv
    wph
    vx
    vy
    cA
    cB
    cR
    cF
    cX
    cY
    qlift.1
    qlift.2
    qlift.3
    qlift.4
    qliftfun.4
    qliftfun
    mpbird
end
