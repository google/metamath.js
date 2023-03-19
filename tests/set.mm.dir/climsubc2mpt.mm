include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "adantr.mm"
include "climconstmpt.mm"
include "climsubmpt.mm"

theorem climsubc2mpt
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cM: class M
  let cZ: class Z
  assume climsubc2mpt.k: |- F/ k ph
  assume climsubc2mpt.z: |- Z = ( ZZ>= ` M )
  assume climsubc2mpt.m: |- ( ph -> M e. ZZ )
  assume climsubc2mpt.a: |- ( ( ph /\ k e. Z ) -> A e. CC )
  assume climsubc2mpt.c: |- ( ph -> ( k e. Z |-> A ) ~~> C )
  assume climsubc2mpt.b: |- ( ph -> B e. CC )

  disjoint B k
  disjoint Z k
  assert |- ( ph -> ( k e. Z |-> ( A - B ) ) ~~> ( C - B ) )

  proof
    wph
    cA
    cB
    cC
    cB
    vk
    cM
    cZ
    climsubc2mpt.k
    climsubc2mpt.z
    climsubc2mpt.m
    climsubc2mpt.a
    wph
    cB
    cc
    wcel
    vk
    cv
    cZ
    wcel
    climsubc2mpt.b
    adantr
    climsubc2mpt.c
    wph
    vk
    cB
    cM
    cZ
    climsubc2mpt.m
    climsubc2mpt.z
    climsubc2mpt.b
    climconstmpt
    climsubmpt
end
