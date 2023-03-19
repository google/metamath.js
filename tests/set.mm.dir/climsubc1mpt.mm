include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "adantr.mm"
include "climconstmpt.mm"
include "climsubmpt.mm"

theorem climsubc1mpt
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cM: class M
  let cZ: class Z
  assume climsubc1mpt.k: |- F/ k ph
  assume climsubc1mpt.z: |- Z = ( ZZ>= ` M )
  assume climsubc1mpt.m: |- ( ph -> M e. ZZ )
  assume climsubc1mpt.b: |- ( ph -> A e. CC )
  assume climsubc1mpt.a: |- ( ( ph /\ k e. Z ) -> B e. CC )
  assume climsubc1mpt.c: |- ( ph -> ( k e. Z |-> B ) ~~> C )

  disjoint A k
  disjoint Z k
  assert |- ( ph -> ( k e. Z |-> ( A - B ) ) ~~> ( A - C ) )

  proof
    wph
    cA
    cB
    cA
    cC
    vk
    cM
    cZ
    climsubc1mpt.k
    climsubc1mpt.z
    climsubc1mpt.m
    wph
    cA
    cc
    wcel
    vk
    cv
    cZ
    wcel
    climsubc1mpt.b
    adantr
    climsubc1mpt.a
    wph
    vk
    cA
    cM
    cZ
    climsubc1mpt.m
    climsubc1mpt.z
    climsubc1mpt.b
    climconstmpt
    climsubc1mpt.c
    climsubmpt
end
