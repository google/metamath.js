include "cv.mm"
include "cfv.mm"
include "cuni.mm"
include "ctop.mm"
include "wcel.mm"
include "ctopon.mm"
include "ccn.mm"
include "co.mm"
include "cntop1.mm"
include "syl.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "cmpt.mm"
include "wf.mm"
include "cnf.mm"
include "feqmptd.mm"
include "eqeltrrd.mm"
include "fveq2.mm"
include "cnmpt21.mm"

theorem cnmpt21f
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cX: class X
  let cY: class Y
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N
  let cP: class P
  let cW: class W
  let cZ: class Z
  assume cnmpt21.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume cnmpt21.k: |- ( ph -> K e. ( TopOn ` Y ) )
  assume cnmpt21.a: |- ( ph -> ( x e. X , y e. Y |-> A ) e. ( ( J tX K ) Cn L ) )
  assume cnmpt21f.f: |- ( ph -> F e. ( L Cn M ) )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint L x
  disjoint L y
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint M x
  disjoint M y
  disjoint Y x
  disjoint Y y
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
  disjoint y z
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
  disjoint M z
  disjoint N v
  disjoint N w
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint P x
  disjoint P y
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
  disjoint Z x
  disjoint Z y
  disjoint Z z
  assert |- ( ph -> ( x e. X , y e. Y |-> ( F ` A ) ) e. ( ( J tX K ) Cn M ) )

  proof
    wph
    vx
    vy
    vz
    cA
    vz
    cv
    #
    cF
    cfv
    #
    cA
    cF
    cfv
    cJ
    cK
    cL
    cM
    cX
    cY
    cL
    cuni
    #
    cnmpt21.j
    cnmpt21.k
    cnmpt21.a
    wph
    cL
    ctop
    wcel
    #
    cL
    @2
    ctopon
    cfv
    wcel
    wph
    cF
    cL
    cM
    ccn
    co
    #
    wcel
    #
    @3
    cnmpt21f.f
    cF
    cL
    cM
    cntop1
    syl
    cL
    @2
    @2
    eqid
    #
    toptopon
    sylib
    wph
    cF
    vz
    @2
    @1
    cmpt
    @4
    wph
    vz
    @2
    cM
    cuni
    #
    cF
    wph
    @5
    @2
    @7
    cF
    wf
    cnmpt21f.f
    cF
    cL
    cM
    @2
    @7
    @6
    @7
    eqid
    cnf
    syl
    feqmptd
    cnmpt21f.f
    eqeltrrd
    @0
    cA
    cF
    fveq2
    cnmpt21
end
