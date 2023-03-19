include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "cfv.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "crio.mm"
include "cpo.mm"
include "biid.mm"
include "wss.mm"
include "ssrab2.mm"
include "a1i.mm"
include "lubval.mm"
include "lublecllem.mm"
include "riota5.mm"
include "eqtrd.mm"

theorem lubid
  let wph: wff ph
  let vy: setvar y
  let cB: class B
  let cU: class U
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let vw: setvar w
  let vx: setvar x
  let vz: setvar z
  assume lubid.b: |- B = ( Base ` K )
  assume lubid.l: |- .<_ = ( le ` K )
  assume lubid.u: |- U = ( lub ` K )
  assume lubid.k: |- ( ph -> K e. Poset )
  assume lubid.x: |- ( ph -> X e. B )

  disjoint .<_ y
  disjoint B y
  disjoint X y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint .<_ w
  disjoint x y
  disjoint x z
  disjoint .<_ x
  disjoint y z
  disjoint .<_ z
  disjoint B w
  disjoint B x
  disjoint B z
  disjoint K w
  disjoint K x
  disjoint K z
  disjoint X w
  disjoint X x
  disjoint X z
  disjoint ph w
  disjoint ph x
  assert |- ( ph -> ( U ` { y e. B | y .<_ X } ) = X )

  proof
    wph
    vy
    cv
    cX
    c.le
    wbr
    #
    vy
    cB
    crab
    #
    cU
    cfv
    vz
    cv
    #
    vx
    cv
    #
    c.le
    wbr
    vz
    @1
    wral
    @2
    vw
    cv
    #
    c.le
    wbr
    vz
    @1
    wral
    @3
    @4
    c.le
    wbr
    wi
    vw
    cB
    wral
    wa
    #
    vx
    cB
    crio
    cX
    wph
    @5
    vx
    vz
    vw
    cB
    @1
    cU
    cK
    c.le
    cpo
    lubid.b
    lubid.l
    lubid.u
    @5
    biid
    lubid.k
    @1
    cB
    wss
    wph
    @0
    vy
    cB
    ssrab2
    a1i
    lubval
    wph
    @5
    vx
    cB
    cX
    lubid.x
    wph
    vx
    vy
    vz
    vw
    cB
    cU
    cK
    c.le
    cX
    lubid.b
    lubid.l
    lubid.u
    lubid.k
    lubid.x
    lublecllem
    riota5
    eqtrd
end
