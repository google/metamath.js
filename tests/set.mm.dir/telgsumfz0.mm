include "cc0.mm"
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
include "weq.mm"
include "wceq.mm"
include "adantl.mm"
include "csbied.mm"
include "eqcomd.mm"
include "cvv.mm"
include "ovexd.mm"
include "oveq12d.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "telgsumfz0s.mm"
include "c0ex.mm"
include "a1i.mm"
include "3eqtrd.mm"

theorem telgsumfz0
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let vi: setvar i
  let vk: setvar k
  let cE: class E
  let cG: class G
  let cK: class K
  let c.mi: class .-
  assume telgsumfz0.k: |- K = ( Base ` G )
  assume telgsumfz0.g: |- ( ph -> G e. Abel )
  assume telgsumfz0.m: |- .- = ( -g ` G )
  assume telgsumfz0.s: |- ( ph -> S e. NN0 )
  assume telgsumfz0.f: |- ( ph -> A. k e. ( 0 ... ( S + 1 ) ) A e. K )
  assume telgsumfz0.a: |- ( k = i -> A = B )
  assume telgsumfz0.c: |- ( k = ( i + 1 ) -> A = C )
  assume telgsumfz0.d: |- ( k = 0 -> A = D )
  assume telgsumfz0.e: |- ( k = ( S + 1 ) -> A = E )

  disjoint A i
  disjoint B k
  disjoint C k
  disjoint D k
  disjoint E k
  disjoint G i
  disjoint K i
  disjoint K k
  disjoint i k
  disjoint S i
  disjoint S k
  disjoint .- i
  disjoint i ph
  disjoint k ph
  assert |- ( ph -> ( G gsum ( i e. ( 0 ... S ) |-> ( B .- C ) ) ) = ( D .- E ) )

  proof
    wph
    cG
    vi
    cc0
    cS
    cfz
    co
    #
    cB
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
    cc0
    cA
    csb
    #
    vk
    cS
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
    cB
    @4
    cC
    @6
    c.mi
    @13
    @4
    cB
    @13
    vk
    @3
    cA
    cB
    @0
    wph
    @12
    simpr
    vk
    vi
    weq
    cA
    cB
    wceq
    @13
    telgsumfz0.a
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
    vk
    cv
    #
    @5
    wceq
    cA
    cC
    wceq
    @13
    telgsumfz0.c
    adantl
    csbied
    eqcomd
    oveq12d
    mpteq2dva
    oveq2d
    wph
    cK
    cA
    cS
    vi
    vk
    cG
    c.mi
    telgsumfz0.k
    telgsumfz0.g
    telgsumfz0.m
    telgsumfz0.s
    telgsumfz0.f
    telgsumfz0s
    wph
    @9
    cD
    @11
    cE
    c.mi
    wph
    vk
    cc0
    cA
    cD
    cvv
    cc0
    cvv
    wcel
    wph
    c0ex
    a1i
    @14
    cc0
    wceq
    cA
    cD
    wceq
    wph
    telgsumfz0.d
    adantl
    csbied
    wph
    vk
    @10
    cA
    cE
    cvv
    wph
    cS
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
    telgsumfz0.e
    adantl
    csbied
    oveq12d
    3eqtrd
end
