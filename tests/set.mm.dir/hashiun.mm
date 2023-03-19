include "ciun.mm"
include "c1.mm"
include "csu.mm"
include "chash.mm"
include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "1cnd.mm"
include "fsumiun.mm"
include "cmul.mm"
include "co.mm"
include "cfn.mm"
include "cc.mm"
include "wceq.mm"
include "wral.mm"
include "ralrimiva.mm"
include "iunfi.mm"
include "syl2anc.mm"
include "ax-1cn.mm"
include "fsumconst.mm"
include "sylancl.mm"
include "cn0.mm"
include "hashcl.mm"
include "nn0cn.mm"
include "mulid1.mm"
include "4syl.mm"
include "eqtrd.mm"
include "sumeq2dv.mm"
include "3eqtr3d.mm"

theorem hashiun
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vu: setvar u
  let vw: setvar w
  let vz: setvar z
  let cC: class C
  assume fsumiun.1: |- ( ph -> A e. Fin )
  assume fsumiun.2: |- ( ( ph /\ x e. A ) -> B e. Fin )
  assume fsumiun.3: |- ( ph -> Disj_ x e. A B )

  disjoint A x
  disjoint ph x
  disjoint k u
  disjoint k w
  disjoint k x
  disjoint k z
  disjoint A k
  disjoint u w
  disjoint u x
  disjoint u z
  disjoint A u
  disjoint w x
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A z
  disjoint B k
  disjoint B u
  disjoint B w
  disjoint B z
  disjoint k ph
  disjoint ph u
  disjoint ph w
  disjoint ph z
  disjoint C u
  disjoint C w
  disjoint C x
  disjoint C z
  assert |- ( ph -> ( # ` U_ x e. A B ) = sum_ x e. A ( # ` B ) )

  proof
    wph
    vx
    cA
    cB
    ciun
    #
    c1
    vk
    csu
    #
    cA
    cB
    c1
    vk
    csu
    #
    vx
    csu
    @0
    chash
    cfv
    #
    cA
    cB
    chash
    cfv
    #
    vx
    csu
    wph
    vx
    cA
    cB
    c1
    vk
    fsumiun.1
    fsumiun.2
    fsumiun.3
    wph
    vx
    cv
    cA
    wcel
    #
    vk
    cv
    cB
    wcel
    wa
    wa
    1cnd
    fsumiun
    wph
    @1
    @3
    c1
    cmul
    co
    #
    @3
    wph
    @0
    cfn
    wcel
    #
    c1
    cc
    wcel
    #
    @1
    @6
    wceq
    wph
    cA
    cfn
    wcel
    cB
    cfn
    wcel
    #
    vx
    cA
    wral
    @7
    fsumiun.1
    wph
    @9
    vx
    cA
    fsumiun.2
    ralrimiva
    vx
    cA
    cB
    iunfi
    syl2anc
    #
    ax-1cn
    @0
    c1
    vk
    fsumconst
    sylancl
    wph
    @7
    @3
    cn0
    wcel
    @3
    cc
    wcel
    @6
    @3
    wceq
    @10
    @0
    hashcl
    @3
    nn0cn
    @3
    mulid1
    4syl
    eqtrd
    wph
    cA
    @2
    @4
    vx
    wph
    @5
    wa
    #
    @2
    @4
    c1
    cmul
    co
    #
    @4
    @11
    @9
    @8
    @2
    @12
    wceq
    fsumiun.2
    ax-1cn
    cB
    c1
    vk
    fsumconst
    sylancl
    @11
    @9
    @4
    cn0
    wcel
    @4
    cc
    wcel
    @12
    @4
    wceq
    fsumiun.2
    cB
    hashcl
    @4
    nn0cn
    @4
    mulid1
    4syl
    eqtrd
    sumeq2dv
    3eqtr3d
end
