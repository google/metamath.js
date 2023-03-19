include "ccj.mm"
include "cc.mm"
include "rlimmptrcl.mm"
include "cmpt.mm"
include "crli.mm"
include "wbr.mm"
include "wcel.mm"
include "rlimcl.mm"
include "syl.mm"
include "wf.mm"
include "cjf.mm"
include "a1i.mm"
include "cv.mm"
include "crp.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "cjcn2.mm"
include "sylan.mm"
include "rlimcn1b.mm"

theorem rlimcj
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume rlimabs.1: |- ( ( ph /\ k e. A ) -> B e. V )
  assume rlimabs.2: |- ( ph -> ( k e. A |-> B ) ~~>r C )

  disjoint A k
  disjoint k ph
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( k e. A |-> ( * ` B ) ) ~~>r ( * ` C ) )

  proof
    wph
    vx
    vy
    vz
    cA
    cB
    cC
    vk
    ccj
    cc
    wph
    cA
    cB
    cC
    vk
    cV
    rlimabs.1
    rlimabs.2
    rlimmptrcl
    wph
    vk
    cA
    cB
    cmpt
    #
    cC
    crli
    wbr
    cC
    cc
    wcel
    #
    rlimabs.2
    cC
    @0
    rlimcl
    syl
    #
    rlimabs.2
    cc
    cc
    ccj
    wf
    wph
    cjf
    a1i
    wph
    @1
    vx
    cv
    #
    crp
    wcel
    vz
    cv
    #
    cC
    cmin
    co
    cabs
    cfv
    vy
    cv
    clt
    wbr
    @4
    ccj
    cfv
    cC
    ccj
    cfv
    cmin
    co
    cabs
    cfv
    @3
    clt
    wbr
    wi
    vz
    cc
    wral
    vy
    crp
    wrex
    @2
    vx
    vy
    vz
    cC
    cjcn2
    sylan
    rlimcn1b
end
