include "ciun.mm"
include "chash.mm"
include "cfv.mm"
include "csu.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfn.mm"
include "wral.mm"
include "3expa.mm"
include "ralrimiva.mm"
include "iunfi.mm"
include "syl2anc.mm"
include "hashiun.mm"
include "sumeq2dv.mm"
include "eqtrd.mm"

theorem hash2iun
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume hash2iun.a: |- ( ph -> A e. Fin )
  assume hash2iun.b: |- ( ( ph /\ x e. A ) -> B e. Fin )
  assume hash2iun.c: |- ( ( ph /\ x e. A /\ y e. B ) -> C e. Fin )
  assume hash2iun.da: |- ( ph -> Disj_ x e. A U_ y e. B C )
  assume hash2iun.db: |- ( ( ph /\ x e. A ) -> Disj_ y e. B C )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( # ` U_ x e. A U_ y e. B C ) = sum_ x e. A sum_ y e. B ( # ` C ) )

  proof
    wph
    vx
    cA
    vy
    cB
    cC
    ciun
    #
    ciun
    chash
    cfv
    cA
    @0
    chash
    cfv
    #
    vx
    csu
    cA
    cB
    cC
    chash
    cfv
    vy
    csu
    #
    vx
    csu
    wph
    vx
    cA
    @0
    hash2iun.a
    wph
    vx
    cv
    cA
    wcel
    #
    wa
    #
    cB
    cfn
    wcel
    cC
    cfn
    wcel
    #
    vy
    cB
    wral
    @0
    cfn
    wcel
    hash2iun.b
    @4
    @5
    vy
    cB
    wph
    @3
    vy
    cv
    cB
    wcel
    @5
    hash2iun.c
    3expa
    #
    ralrimiva
    vy
    cB
    cC
    iunfi
    syl2anc
    hash2iun.da
    hashiun
    wph
    cA
    @1
    @2
    vx
    @4
    vy
    cB
    cC
    hash2iun.b
    @6
    hash2iun.db
    hashiun
    sumeq2dv
    eqtrd
end
