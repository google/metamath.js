include "cmpt2.mm"
include "cxp.mm"
include "cmpt.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "eqidd.mm"
include "mpt2mpt.mm"
include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "txtopon.mm"
include "syl2anc.mm"
include "cnmptc.mm"
include "syl5eqelr.mm"

theorem cnmpt2c
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cJ: class J
  let cK: class K
  let cL: class L
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cM: class M
  let cN: class N
  let cW: class W
  assume cnmpt21.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume cnmpt21.k: |- ( ph -> K e. ( TopOn ` Y ) )
  assume cnmpt2c.l: |- ( ph -> L e. ( TopOn ` Z ) )
  assume cnmpt2c.p: |- ( ph -> P e. Z )

  disjoint x y
  disjoint L x
  disjoint L y
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint P x
  disjoint P y
  disjoint Y x
  disjoint Y y
  disjoint Z x
  disjoint Z y
  disjoint u v
  disjoint u w
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v z
  disjoint A v
  disjoint w z
  disjoint A w
  disjoint A z
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint C u
  disjoint C v
  disjoint D w
  disjoint D z
  disjoint J v
  disjoint J z
  disjoint w x
  disjoint w y
  disjoint F w
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint v x
  disjoint v y
  disjoint L v
  disjoint L w
  disjoint L z
  disjoint ph v
  disjoint ph z
  disjoint u x
  disjoint u y
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X z
  disjoint M v
  disjoint M w
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint N v
  disjoint N w
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint P z
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y z
  disjoint K v
  disjoint K z
  disjoint W v
  disjoint W w
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint Z u
  disjoint Z v
  disjoint Z w
  disjoint Z z
  assert |- ( ph -> ( x e. X , y e. Y |-> P ) e. ( ( J tX K ) Cn L ) )

  proof
    wph
    vx
    vy
    cX
    cY
    cP
    cmpt2
    vz
    cX
    cY
    cxp
    #
    cP
    cmpt
    cJ
    cK
    ctx
    co
    #
    cL
    ccn
    co
    vx
    vy
    vz
    cX
    cY
    cP
    cP
    vz
    cv
    vx
    cv
    vy
    cv
    cop
    wceq
    cP
    eqidd
    mpt2mpt
    wph
    vz
    cP
    @1
    cL
    @0
    cZ
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    cK
    cY
    ctopon
    cfv
    wcel
    @1
    @0
    ctopon
    cfv
    wcel
    cnmpt21.j
    cnmpt21.k
    cJ
    cK
    cX
    cY
    txtopon
    syl2anc
    cnmpt2c.l
    cnmpt2c.p
    cnmptc
    syl5eqelr
end
