include "cmin.mm"
include "cc.mm"
include "rlimmptrcl.mm"
include "cmpt.mm"
include "crli.mm"
include "wbr.mm"
include "wcel.mm"
include "rlimcl.mm"
include "syl.mm"
include "cxp.mm"
include "wf.mm"
include "subf.mm"
include "a1i.mm"
include "cv.mm"
include "crp.mm"
include "wa.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "simpr.mm"
include "adantr.mm"
include "subcn2.mm"
include "syl3anc.mm"
include "rlimcn2.mm"

theorem rlimsub
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cV: class V
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  assume rlimadd.3: |- ( ( ph /\ x e. A ) -> B e. V )
  assume rlimadd.4: |- ( ( ph /\ x e. A ) -> C e. V )
  assume rlimadd.5: |- ( ph -> ( x e. A |-> B ) ~~>r D )
  assume rlimadd.6: |- ( ph -> ( x e. A |-> C ) ~~>r E )

  disjoint A x
  disjoint D x
  disjoint ph x
  disjoint E x
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint C v
  disjoint C w
  disjoint C y
  disjoint C z
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D y
  disjoint D z
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint E u
  disjoint E v
  disjoint E w
  disjoint E y
  disjoint E z
  assert |- ( ph -> ( x e. A |-> ( B - C ) ) ~~>r ( D - E ) )

  proof
    wph
    vy
    vx
    vv
    vu
    cA
    cB
    cC
    cD
    cE
    cmin
    cc
    cc
    vw
    vz
    wph
    cA
    cB
    cD
    vx
    cV
    rlimadd.3
    rlimadd.5
    rlimmptrcl
    wph
    cA
    cC
    cE
    vx
    cV
    rlimadd.4
    rlimadd.6
    rlimmptrcl
    wph
    vx
    cA
    cB
    cmpt
    #
    cD
    crli
    wbr
    cD
    cc
    wcel
    #
    rlimadd.5
    cD
    @0
    rlimcl
    syl
    #
    wph
    vx
    cA
    cC
    cmpt
    #
    cE
    crli
    wbr
    cE
    cc
    wcel
    #
    rlimadd.6
    cE
    @3
    rlimcl
    syl
    #
    rlimadd.5
    rlimadd.6
    cc
    cc
    cxp
    cc
    cmin
    wf
    wph
    subf
    a1i
    wph
    vy
    cv
    #
    crp
    wcel
    #
    wa
    @7
    @1
    @4
    vu
    cv
    #
    cD
    cmin
    co
    cabs
    cfv
    vz
    cv
    clt
    wbr
    vv
    cv
    #
    cE
    cmin
    co
    cabs
    cfv
    vw
    cv
    clt
    wbr
    wa
    @8
    @9
    cmin
    co
    cD
    cE
    cmin
    co
    cmin
    co
    cabs
    cfv
    @6
    clt
    wbr
    wi
    vv
    cc
    wral
    vu
    cc
    wral
    vw
    crp
    wrex
    vz
    crp
    wrex
    wph
    @7
    simpr
    wph
    @1
    @7
    @2
    adantr
    wph
    @4
    @7
    @5
    adantr
    vz
    vw
    vv
    vu
    @6
    cD
    cE
    subcn2
    syl3anc
    rlimcn2
end
