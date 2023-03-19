include "cv.mm"
include "co.mm"
include "cuni.mm"
include "ctop.mm"
include "wcel.mm"
include "ctopon.mm"
include "cfv.mm"
include "cmpt2.mm"
include "ctx.mm"
include "ccn.mm"
include "cntop2.mm"
include "syl.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "cxp.mm"
include "wfn.mm"
include "wceq.mm"
include "wf.mm"
include "txtopon.mm"
include "syl2anc.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "ffn.mm"
include "fnov.mm"
include "eqeltrrd.mm"
include "oveq12.mm"
include "cnmpt22.mm"

theorem cnmpt22f
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cC: class C
  let cD: class D
  let cP: class P
  let cW: class W
  let cZ: class Z
  assume cnmpt21.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume cnmpt21.k: |- ( ph -> K e. ( TopOn ` Y ) )
  assume cnmpt21.a: |- ( ph -> ( x e. X , y e. Y |-> A ) e. ( ( J tX K ) Cn L ) )
  assume cnmpt2t.b: |- ( ph -> ( x e. X , y e. Y |-> B ) e. ( ( J tX K ) Cn M ) )
  assume cnmpt22f.f: |- ( ph -> F e. ( ( L tX M ) Cn N ) )

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
  disjoint N x
  disjoint N y
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
  disjoint B z
  disjoint C x
  disjoint C y
  assert |- ( ph -> ( x e. X , y e. Y |-> ( A F B ) ) e. ( ( J tX K ) Cn N ) )

  proof
    wph
    vx
    vy
    vz
    vw
    cA
    cB
    vz
    cv
    #
    vw
    cv
    #
    cF
    co
    #
    cA
    cB
    cF
    co
    cJ
    cK
    cL
    cM
    cN
    cM
    cuni
    #
    cX
    cY
    cL
    cuni
    #
    cnmpt21.j
    cnmpt21.k
    cnmpt21.a
    cnmpt2t.b
    wph
    cL
    ctop
    wcel
    #
    cL
    @4
    ctopon
    cfv
    wcel
    #
    wph
    vx
    vy
    cX
    cY
    cA
    cmpt2
    #
    cJ
    cK
    ctx
    co
    #
    cL
    ccn
    co
    wcel
    @5
    cnmpt21.a
    @7
    @8
    cL
    cntop2
    syl
    cL
    @4
    @4
    eqid
    toptopon
    sylib
    #
    wph
    cM
    ctop
    wcel
    #
    cM
    @3
    ctopon
    cfv
    wcel
    #
    wph
    vx
    vy
    cX
    cY
    cB
    cmpt2
    #
    @8
    cM
    ccn
    co
    wcel
    @10
    cnmpt2t.b
    @12
    @8
    cM
    cntop2
    syl
    cM
    @3
    @3
    eqid
    toptopon
    sylib
    #
    wph
    cF
    vz
    vw
    @4
    @3
    @2
    cmpt2
    #
    cL
    cM
    ctx
    co
    #
    cN
    ccn
    co
    #
    wph
    cF
    @4
    @3
    cxp
    #
    wfn
    #
    cF
    @14
    wceq
    wph
    @17
    cN
    cuni
    #
    cF
    wf
    #
    @18
    wph
    @15
    @17
    ctopon
    cfv
    wcel
    #
    cN
    @19
    ctopon
    cfv
    wcel
    #
    cF
    @16
    wcel
    #
    @20
    wph
    @6
    @11
    @21
    @9
    @13
    cL
    cM
    @4
    @3
    txtopon
    syl2anc
    wph
    cN
    ctop
    wcel
    #
    @22
    wph
    @23
    @24
    cnmpt22f.f
    cF
    @15
    cN
    cntop2
    syl
    cN
    @19
    @19
    eqid
    toptopon
    sylib
    cnmpt22f.f
    cF
    @15
    cN
    @17
    @19
    cnf2
    syl3anc
    @17
    @19
    cF
    ffn
    syl
    vz
    vw
    @4
    @3
    cF
    fnov
    sylib
    cnmpt22f.f
    eqeltrrd
    @0
    cA
    @1
    cB
    cF
    oveq12
    cnmpt22
end
