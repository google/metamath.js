include "co.mm"
include "cmpt.mm"
include "cop.mm"
include "cfv.mm"
include "ccn.mm"
include "df-ov.mm"
include "mpteq2i.mm"
include "ctx.mm"
include "cnmpt1t.mm"
include "cnmpt11f.mm"
include "syl5eqel.mm"

theorem cnmpt12f
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let cY: class Y
  let cZ: class Z
  let cP: class P
  let cC: class C
  assume cnmptid.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume cnmpt11.a: |- ( ph -> ( x e. X |-> A ) e. ( J Cn K ) )
  assume cnmpt1t.b: |- ( ph -> ( x e. X |-> B ) e. ( J Cn L ) )
  assume cnmpt12f.f: |- ( ph -> F e. ( ( K tX L ) Cn M ) )

  disjoint F x
  disjoint ph x
  disjoint J x
  disjoint M x
  disjoint X x
  disjoint K x
  disjoint L x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B z
  disjoint D y
  disjoint D z
  disjoint x y
  disjoint F y
  disjoint J y
  disjoint x z
  disjoint M y
  disjoint M z
  disjoint X y
  disjoint X z
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint K y
  disjoint L y
  disjoint P x
  disjoint P y
  disjoint B y
  disjoint C x
  assert |- ( ph -> ( x e. X |-> ( A F B ) ) e. ( J Cn M ) )

  proof
    wph
    vx
    cX
    cA
    cB
    cF
    co
    #
    cmpt
    vx
    cX
    cA
    cB
    cop
    #
    cF
    cfv
    #
    cmpt
    cJ
    cM
    ccn
    co
    vx
    cX
    @0
    @2
    cA
    cB
    cF
    df-ov
    mpteq2i
    wph
    vx
    @1
    cF
    cJ
    cK
    cL
    ctx
    co
    cM
    cX
    cnmptid.j
    wph
    vx
    cA
    cB
    cJ
    cK
    cL
    cX
    cnmptid.j
    cnmpt11.a
    cnmpt1t.b
    cnmpt1t
    cnmpt12f.f
    cnmpt11f
    syl5eqel
end
