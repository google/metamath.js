include "cn0.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cv.mm"
include "csb.mm"
include "c1.mm"
include "caddc.mm"
include "cc0.mm"
include "wcel.mm"
include "wa.mm"
include "simpr.mm"
include "weq.mm"
include "wceq.mm"
include "adantl.mm"
include "csbied.mm"
include "eqcomd.mm"
include "peano2nn0.mm"
include "oveq12d.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "telgsums.mm"
include "cvv.mm"
include "c0ex.mm"
include "a1i.mm"
include "3eqtrd.mm"

theorem telgsum
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
  let c.mi: class .-
  let c.0: class .0.
  assume telgsum.b: |- B = ( Base ` G )
  assume telgsum.g: |- ( ph -> G e. Abel )
  assume telgsum.m: |- .- = ( -g ` G )
  assume telgsum.0: |- .0. = ( 0g ` G )
  assume telgsum.f: |- ( ph -> A. k e. NN0 A e. B )
  assume telgsum.s: |- ( ph -> S e. NN0 )
  assume telgsum.u: |- ( ph -> A. k e. NN0 ( S < k -> A = .0. ) )
  assume telgsum.c: |- ( k = i -> A = C )
  assume telgsum.d: |- ( k = ( i + 1 ) -> A = D )
  assume telgsum.e: |- ( k = 0 -> A = E )

  disjoint A i
  disjoint B i
  disjoint B k
  disjoint i k
  disjoint C k
  disjoint D k
  disjoint E k
  disjoint G i
  disjoint S i
  disjoint S k
  disjoint i ph
  disjoint k ph
  disjoint .0. i
  disjoint .0. k
  disjoint .- i
  assert |- ( ph -> ( G gsum ( i e. NN0 |-> ( C .- D ) ) ) = E )

  proof
    wph
    cG
    vi
    cn0
    cC
    cD
    c.mi
    co
    #
    cmpt
    #
    cgsu
    co
    cG
    vi
    cn0
    vk
    vi
    cv
    #
    cA
    csb
    #
    vk
    @2
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
    cE
    wph
    @1
    @7
    cG
    cgsu
    wph
    vi
    cn0
    @0
    @6
    wph
    @2
    cn0
    wcel
    #
    wa
    #
    cC
    @3
    cD
    @5
    c.mi
    @9
    @3
    cC
    @9
    vk
    @2
    cA
    cC
    cn0
    wph
    @8
    simpr
    vk
    vi
    weq
    cA
    cC
    wceq
    @9
    telgsum.c
    adantl
    csbied
    eqcomd
    @9
    @5
    cD
    @9
    vk
    @4
    cA
    cD
    cn0
    @8
    @4
    cn0
    wcel
    wph
    @2
    peano2nn0
    adantl
    vk
    cv
    #
    @4
    wceq
    cA
    cD
    wceq
    @9
    telgsum.d
    adantl
    csbied
    eqcomd
    oveq12d
    mpteq2dva
    oveq2d
    wph
    cB
    cA
    cS
    vi
    vk
    cG
    c.mi
    c.0
    telgsum.b
    telgsum.g
    telgsum.m
    telgsum.0
    telgsum.f
    telgsum.s
    telgsum.u
    telgsums
    wph
    vk
    cc0
    cA
    cE
    cvv
    cc0
    cvv
    wcel
    wph
    c0ex
    a1i
    @10
    cc0
    wceq
    cA
    cE
    wceq
    wph
    telgsum.e
    adantl
    csbied
    3eqtrd
end
