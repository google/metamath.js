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
include "climeldmeq.mm"

theorem climeldmeqf
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vj: setvar j
  assume climeldmeqf.p: |- F/ k ph
  assume climeldmeqf.n: |- F/_ k F
  assume climeldmeqf.o: |- F/_ k G
  assume climeldmeqf.z: |- Z = ( ZZ>= ` M )
  assume climeldmeqf.f: |- ( ph -> F e. V )
  assume climeldmeqf.g: |- ( ph -> G e. W )
  assume climeldmeqf.m: |- ( ph -> M e. ZZ )
  assume climeldmeqf.e: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = ( G ` k ) )

  disjoint Z k
  disjoint F j
  disjoint G j
  disjoint Z j
  disjoint j k
  disjoint j ph
  assert |- ( ph -> ( F e. dom ~~> <-> G e. dom ~~> ) )

  proof
    wph
    vj
    cF
    cG
    cM
    cV
    cW
    cZ
    climeldmeqf.z
    climeldmeqf.f
    climeldmeqf.g
    climeldmeqf.m
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
    climeldmeqf.p
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
    climeldmeqf.n
    vk
    @6
    nfcv
    #
    nffv
    vk
    @6
    cG
    climeldmeqf.o
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
    climeldmeqf.e
    chvar
    climeldmeq
end
