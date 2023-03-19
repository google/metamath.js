include "cin.mm"
include "cdiv.mm"
include "co.mm"
include "cmpt.mm"
include "c1.mm"
include "cmul.mm"
include "csmblfn.mm"
include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "elinel1.mm"
include "adantl.mm"
include "syldan.mm"
include "recnd.mm"
include "cc0.mm"
include "wne.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "elinel2.mm"
include "sseldi.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "rabidim2.mm"
include "syl.mm"
include "divrecd.mm"
include "mpteq2da.mm"
include "1red.mm"
include "sseli.mm"
include "redivcld.mm"
include "smfrec.mm"
include "smfmul.mm"
include "eqeltrd.mm"

theorem smfdiv
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cE: class E
  let cV: class V
  let cW: class W
  let vk: setvar k
  assume smfdiv.x: |- F/ x ph
  assume smfdiv.s: |- ( ph -> S e. SAlg )
  assume smfdiv.a: |- ( ph -> A e. V )
  assume smfdiv.b: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume smfdiv.c: |- ( ph -> C e. W )
  assume smfdiv.d: |- ( ( ph /\ x e. C ) -> D e. RR )
  assume smfdiv.m: |- ( ph -> ( x e. A |-> B ) e. ( SMblFn ` S ) )
  assume smfdiv.n: |- ( ph -> ( x e. C |-> D ) e. ( SMblFn ` S ) )
  assume smfdiv.e: |- E = { x e. C | D =/= 0 }

  disjoint A x
  disjoint C x
  disjoint E x
  disjoint k x
  assert |- ( ph -> ( x e. ( A i^i E ) |-> ( B / D ) ) e. ( SMblFn ` S ) )

  proof
    wph
    vx
    cA
    cE
    cin
    #
    cB
    cD
    cdiv
    co
    #
    cmpt
    vx
    @0
    cB
    c1
    cD
    cdiv
    co
    #
    cmul
    co
    #
    cmpt
    cS
    csmblfn
    cfv
    wph
    vx
    @0
    @1
    @3
    smfdiv.x
    wph
    vx
    cv
    #
    @0
    wcel
    #
    wa
    #
    cB
    cD
    @6
    cB
    wph
    @5
    @4
    cA
    wcel
    #
    cB
    cr
    wcel
    @5
    @7
    wph
    @4
    cA
    cE
    elinel1
    adantl
    smfdiv.b
    syldan
    recnd
    @6
    cD
    wph
    @5
    @4
    cC
    wcel
    #
    cD
    cr
    wcel
    #
    @5
    @8
    wph
    @5
    cE
    cC
    @4
    cE
    cD
    cc0
    wne
    #
    vx
    cC
    crab
    #
    cC
    smfdiv.e
    @10
    vx
    cC
    ssrab2
    eqsstri
    #
    @4
    cA
    cE
    elinel2
    #
    sseldi
    adantl
    smfdiv.d
    syldan
    recnd
    @5
    @10
    wph
    @5
    @4
    cE
    wcel
    #
    @10
    @13
    @14
    @4
    @11
    wcel
    #
    @10
    @14
    @15
    cE
    @11
    @4
    smfdiv.e
    eleq2i
    biimpi
    @10
    vx
    cC
    rabidim2
    syl
    #
    syl
    adantl
    divrecd
    mpteq2da
    wph
    vx
    cA
    cB
    cE
    @2
    cS
    cV
    smfdiv.x
    smfdiv.s
    smfdiv.a
    smfdiv.b
    wph
    @14
    wa
    #
    c1
    cD
    @17
    1red
    wph
    @14
    @8
    @9
    @14
    @8
    wph
    cE
    cC
    @4
    @12
    sseli
    adantl
    smfdiv.d
    syldan
    @14
    @10
    wph
    @16
    adantl
    redivcld
    smfdiv.m
    wph
    vx
    cC
    cD
    cE
    cS
    cW
    smfdiv.x
    smfdiv.s
    smfdiv.c
    smfdiv.d
    smfdiv.n
    smfdiv.e
    smfrec
    smfmul
    eqeltrd
end
