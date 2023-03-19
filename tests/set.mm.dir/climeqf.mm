include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfeq.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "climeq.mm"

theorem climeqf
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vj: setvar j
  assume climeqf.p: |- F/ k ph
  assume climeqf.k: |- F/_ k F
  assume climeqf.n: |- F/_ k G
  assume climeqf.m: |- ( ph -> M e. ZZ )
  assume climeqf.z: |- Z = ( ZZ>= ` M )
  assume climeqf.f: |- ( ph -> F e. V )
  assume climeqf.g: |- ( ph -> G e. W )
  assume climeqf.e: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = ( G ` k ) )

  disjoint Z k
  disjoint A j
  disjoint F j
  disjoint G j
  disjoint Z j
  disjoint j k
  disjoint j ph
  assert |- ( ph -> ( F ~~> A <-> G ~~> A ) )

  proof
    wph
    cA
    vj
    cF
    cG
    cM
    cV
    cW
    cZ
    climeqf.z
    climeqf.f
    climeqf.g
    climeqf.m
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
    @0
    cG
    cfv
    #
    wceq
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
    @6
    cF
    cfv
    #
    @6
    cG
    cfv
    #
    wceq
    #
    wi
    vk
    vj
    @8
    @11
    vk
    wph
    @7
    vk
    climeqf.p
    @7
    vk
    nfv
    nfan
    vk
    @9
    @10
    vk
    @6
    cF
    climeqf.k
    vk
    @6
    nfcv
    #
    nffv
    vk
    @6
    cG
    climeqf.n
    @12
    nffv
    nfeq
    nfim
    @0
    @6
    wceq
    #
    @2
    @8
    @5
    @11
    @13
    @1
    @7
    wph
    @0
    @6
    cZ
    eleq1
    anbi2d
    @13
    @3
    @9
    @4
    @10
    @0
    @6
    cF
    fveq2
    @0
    @6
    cG
    fveq2
    eqeq12d
    imbi12d
    climeqf.e
    chvar
    climeq
end
