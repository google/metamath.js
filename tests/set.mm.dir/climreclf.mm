include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cr.mm"
include "wi.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfel.mm"
include "nfim.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "climrecl.mm"

theorem climreclf
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  assume climreclf.k: |- F/ k ph
  assume climreclf.f: |- F/_ k F
  assume climreclf.z: |- Z = ( ZZ>= ` M )
  assume climreclf.m: |- ( ph -> M e. ZZ )
  assume climreclf.a: |- ( ph -> F ~~> A )
  assume climreclf.r: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. RR )

  disjoint Z k
  disjoint A j
  disjoint F j
  disjoint M j
  disjoint Z j
  disjoint j k
  disjoint j ph
  assert |- ( ph -> A e. RR )

  proof
    wph
    cA
    vj
    cF
    cM
    cZ
    climreclf.z
    climreclf.m
    climreclf.a
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @0
    cF
    cfv
    #
    cr
    wcel
    #
    wi
    wph
    vj
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @5
    cF
    cfv
    #
    cr
    wcel
    #
    wi
    vk
    vj
    @7
    @9
    vk
    wph
    @6
    vk
    climreclf.k
    @6
    vk
    nfv
    nfan
    vk
    @8
    cr
    vk
    @5
    cF
    climreclf.f
    vk
    @5
    nfcv
    nffv
    vk
    cr
    nfcv
    nfel
    nfim
    @0
    @5
    wceq
    #
    @2
    @7
    @4
    @9
    @10
    @1
    @6
    wph
    @0
    @5
    cZ
    eleq1
    anbi2d
    @10
    @3
    @8
    cr
    @0
    @5
    cF
    fveq2
    eleq1d
    imbi12d
    climreclf.r
    chvar
    climrecl
end
