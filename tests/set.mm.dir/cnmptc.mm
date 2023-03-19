include "cmpt.mm"
include "csn.mm"
include "cxp.mm"
include "ccn.mm"
include "co.mm"
include "fconstmpt.mm"
include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cnconst2.mm"
include "syl3anc.mm"
include "syl5eqelr.mm"

theorem cnmptc
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cD: class D
  let cF: class F
  let cM: class M
  let cZ: class Z
  let cL: class L
  assume cnmptid.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume cnmptc.k: |- ( ph -> K e. ( TopOn ` Y ) )
  assume cnmptc.p: |- ( ph -> P e. Y )

  disjoint ph x
  disjoint J x
  disjoint X x
  disjoint Y x
  disjoint K x
  disjoint P x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B z
  disjoint D y
  disjoint D z
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint J y
  disjoint x z
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint X y
  disjoint X z
  disjoint Y y
  disjoint Y z
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint P y
  assert |- ( ph -> ( x e. X |-> P ) e. ( J Cn K ) )

  proof
    wph
    vx
    cX
    cP
    cmpt
    cX
    cP
    csn
    cxp
    #
    cJ
    cK
    ccn
    co
    #
    vx
    cX
    cP
    fconstmpt
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
    cP
    cY
    wcel
    @0
    @1
    wcel
    cnmptid.j
    cnmptc.k
    cnmptc.p
    cP
    cJ
    cK
    cX
    cY
    cnconst2
    syl3anc
    syl5eqelr
end
