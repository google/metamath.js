include "ciun.mm"
include "chash.mm"
include "cfv.mm"
include "csu.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cfn.mm"
include "diffi.mm"
include "syl.mm"
include "adantr.mm"
include "syl5eqel.mm"
include "hash2iun.mm"
include "2sumeq2dv.mm"
include "cc.mm"
include "wceq.mm"
include "1cnd.mm"
include "fsumconst.mm"
include "syl2anc.mm"
include "sumeq2dv.mm"
include "a1i.mm"
include "fveq2d.mm"
include "hashdifsn.mm"
include "sylan.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "cn0.mm"
include "hashcl.mm"
include "nn0cnd.mm"
include "peano2cnm.mm"
include "mulid1d.mm"
include "sumeq2ad.mm"
include "3eqtrd.mm"

theorem hash2iun1dif1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume hash2iun1dif1.a: |- ( ph -> A e. Fin )
  assume hash2iun1dif1.b: |- B = ( A \ { x } )
  assume hash2iun1dif1.c: |- ( ( ph /\ x e. A /\ y e. B ) -> C e. Fin )
  assume hash2iun1dif1.da: |- ( ph -> Disj_ x e. A U_ y e. B C )
  assume hash2iun1dif1.db: |- ( ( ph /\ x e. A ) -> Disj_ y e. B C )
  assume hash2iun1dif1.1: |- ( ( ph /\ x e. A /\ y e. B ) -> ( # ` C ) = 1 )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( # ` U_ x e. A U_ y e. B C ) = ( ( # ` A ) x. ( ( # ` A ) - 1 ) ) )

  proof
    wph
    vx
    cA
    vy
    cB
    cC
    ciun
    ciun
    chash
    cfv
    cA
    cB
    cC
    chash
    cfv
    #
    vy
    csu
    vx
    csu
    cA
    cB
    c1
    vy
    csu
    #
    vx
    csu
    #
    cA
    chash
    cfv
    #
    @3
    c1
    cmin
    co
    #
    cmul
    co
    #
    wph
    vx
    vy
    cA
    cB
    cC
    hash2iun1dif1.a
    wph
    vx
    cv
    #
    cA
    wcel
    #
    wa
    #
    cB
    cA
    @6
    csn
    #
    cdif
    #
    cfn
    hash2iun1dif1.b
    wph
    @10
    cfn
    wcel
    #
    @7
    wph
    cA
    cfn
    wcel
    #
    @11
    hash2iun1dif1.a
    cA
    @9
    diffi
    syl
    adantr
    syl5eqel
    #
    hash2iun1dif1.c
    hash2iun1dif1.da
    hash2iun1dif1.db
    hash2iun
    wph
    cA
    cB
    @0
    c1
    vx
    vy
    hash2iun1dif1.1
    2sumeq2dv
    wph
    @2
    cA
    cB
    chash
    cfv
    #
    c1
    cmul
    co
    #
    vx
    csu
    cA
    @4
    c1
    cmul
    co
    #
    vx
    csu
    #
    @5
    wph
    cA
    @1
    @15
    vx
    @8
    cB
    cfn
    wcel
    c1
    cc
    wcel
    @1
    @15
    wceq
    @13
    @8
    1cnd
    cB
    c1
    vy
    fsumconst
    syl2anc
    sumeq2dv
    wph
    cA
    @15
    @16
    vx
    @8
    @14
    @4
    c1
    cmul
    @8
    @14
    @10
    chash
    cfv
    #
    @4
    @8
    cB
    @10
    chash
    cB
    @10
    wceq
    @8
    hash2iun1dif1.b
    a1i
    fveq2d
    wph
    @12
    @7
    @18
    @4
    wceq
    hash2iun1dif1.a
    cA
    @6
    hashdifsn
    sylan
    eqtrd
    oveq1d
    sumeq2dv
    wph
    @17
    cA
    @4
    vx
    csu
    #
    @5
    wph
    cA
    @16
    @4
    vx
    wph
    @4
    wph
    @3
    cc
    wcel
    @4
    cc
    wcel
    #
    wph
    @3
    wph
    @12
    @3
    cn0
    wcel
    hash2iun1dif1.a
    cA
    hashcl
    syl
    nn0cnd
    @3
    peano2cnm
    syl
    #
    mulid1d
    sumeq2ad
    wph
    @12
    @20
    @19
    @5
    wceq
    hash2iun1dif1.a
    @21
    cA
    @4
    vx
    fsumconst
    syl2anc
    eqtrd
    3eqtrd
    3eqtrd
end
