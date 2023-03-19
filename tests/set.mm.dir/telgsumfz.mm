include "cfz.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cv.mm"
include "csb.mm"
include "c1.mm"
include "caddc.mm"
include "wcel.mm"
include "wa.mm"
include "simpr.mm"
include "wceq.mm"
include "adantl.mm"
include "csbied.mm"
include "eqcomd.mm"
include "cvv.mm"
include "ovexd.mm"
include "oveq12d.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "telgsumfzs.mm"
include "cuz.mm"
include "elfvexd.mm"
include "3eqtrd.mm"

theorem telgsumfz
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vi: setvar i
  let vk: setvar k
  let cE: class E
  let cG: class G
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let cN: class N
  assume telgsumfz.b: |- B = ( Base ` G )
  assume telgsumfz.g: |- ( ph -> G e. Abel )
  assume telgsumfz.m: |- .- = ( -g ` G )
  assume telgsumfz.n: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume telgsumfz.f: |- ( ph -> A. k e. ( M ... ( N + 1 ) ) A e. B )
  assume telgsumfz.l: |- ( k = i -> A = L )
  assume telgsumfz.c: |- ( k = ( i + 1 ) -> A = C )
  assume telgsumfz.d: |- ( k = M -> A = D )
  assume telgsumfz.e: |- ( k = ( N + 1 ) -> A = E )

  disjoint A i
  disjoint B i
  disjoint B k
  disjoint i k
  disjoint C k
  disjoint D k
  disjoint E k
  disjoint G i
  disjoint L k
  disjoint M i
  disjoint M k
  disjoint N i
  disjoint N k
  disjoint .- i
  disjoint i ph
  disjoint k ph
  assert |- ( ph -> ( G gsum ( i e. ( M ... N ) |-> ( L .- C ) ) ) = ( D .- E ) )

  proof
    wph
    cG
    vi
    cM
    cN
    cfz
    co
    #
    cL
    cC
    c.mi
    co
    #
    cmpt
    #
    cgsu
    co
    cG
    vi
    @0
    vk
    vi
    cv
    #
    cA
    csb
    #
    vk
    @3
    c1
    caddc
    co
    #
    cA
    csb
    #
    c.mi
    co
    #
    cmpt
    #
    cgsu
    co
    vk
    cM
    cA
    csb
    #
    vk
    cN
    c1
    caddc
    co
    #
    cA
    csb
    #
    c.mi
    co
    cD
    cE
    c.mi
    co
    wph
    @2
    @8
    cG
    cgsu
    wph
    vi
    @0
    @1
    @7
    wph
    @3
    @0
    wcel
    #
    wa
    #
    cL
    @4
    cC
    @6
    c.mi
    @13
    @4
    cL
    @13
    vk
    @3
    cA
    cL
    @0
    wph
    @12
    simpr
    vk
    cv
    #
    @3
    wceq
    cA
    cL
    wceq
    @13
    telgsumfz.l
    adantl
    csbied
    eqcomd
    @13
    @6
    cC
    @13
    vk
    @5
    cA
    cC
    cvv
    @13
    @3
    c1
    caddc
    ovexd
    @14
    @5
    wceq
    cA
    cC
    wceq
    @13
    telgsumfz.c
    adantl
    csbied
    eqcomd
    oveq12d
    mpteq2dva
    oveq2d
    wph
    cB
    cA
    vi
    vk
    cG
    cM
    c.mi
    cN
    telgsumfz.b
    telgsumfz.g
    telgsumfz.m
    telgsumfz.n
    telgsumfz.f
    telgsumfzs
    wph
    @9
    cD
    @11
    cE
    c.mi
    wph
    vk
    cM
    cA
    cD
    cvv
    wph
    cN
    cuz
    cM
    telgsumfz.n
    elfvexd
    @14
    cM
    wceq
    cA
    cD
    wceq
    wph
    telgsumfz.d
    adantl
    csbied
    wph
    vk
    @10
    cA
    cE
    cvv
    wph
    cN
    c1
    caddc
    ovexd
    @14
    @10
    wceq
    cA
    cE
    wceq
    wph
    telgsumfz.e
    adantl
    csbied
    oveq12d
    3eqtrd
end
