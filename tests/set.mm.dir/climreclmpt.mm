include "cmpt.mm"
include "nfmpt1.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cr.mm"
include "eqidd.mm"
include "fvmpt2d.mm"
include "eqeltrd.mm"
include "climreclf.mm"

theorem climreclmpt
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cM: class M
  let cZ: class Z
  assume climreclmpt.k: |- F/ k ph
  assume climreclmpt.m: |- ( ph -> M e. ZZ )
  assume climreclmpt.z: |- Z = ( ZZ>= ` M )
  assume climreclmpt.a: |- ( ( ph /\ k e. Z ) -> A e. RR )
  assume climreclmpt.b: |- ( ph -> ( k e. Z |-> A ) ~~> B )

  disjoint Z k
  assert |- ( ph -> B e. RR )

  proof
    wph
    cB
    vk
    vk
    cZ
    cA
    cmpt
    #
    cM
    cZ
    climreclmpt.k
    vk
    cZ
    cA
    nfmpt1
    climreclmpt.z
    climreclmpt.m
    climreclmpt.b
    wph
    vk
    cv
    #
    cZ
    wcel
    wa
    @1
    @0
    cfv
    cA
    cr
    wph
    vk
    cZ
    cA
    @0
    cr
    wph
    @0
    eqidd
    climreclmpt.a
    fvmpt2d
    climreclmpt.a
    eqeltrd
    climreclf
end
