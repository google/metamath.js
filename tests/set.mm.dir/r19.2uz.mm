include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "wral.mm"
include "wrex.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cz.mm"
include "eluzelz.mm"
include "uzid.mm"
include "ne0i.mm"
include "3syl.mm"
include "eleq2s.mm"
include "r19.2z.mm"
include "sylan.mm"
include "uztrn2.mm"
include "ex.mm"
include "anim1d.mm"
include "reximdv2.mm"
include "imp.mm"
include "syldan.mm"
include "rexlimiva.mm"

theorem r19.2uz
  let wph: wff ph
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cZ: class Z
  let vm: setvar m
  assume rexuz3.1: |- Z = ( ZZ>= ` M )

  disjoint M j
  disjoint j ph
  disjoint j k
  disjoint Z j
  disjoint Z k
  disjoint j m
  disjoint M m
  disjoint m ph
  disjoint k m
  disjoint Z m
  assert |- ( E. j e. Z A. k e. ( ZZ>= ` j ) ph -> E. k e. Z ph )

  proof
    wph
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    wph
    vk
    cZ
    wrex
    #
    vj
    cZ
    @0
    cZ
    wcel
    #
    @2
    wph
    vk
    @1
    wrex
    #
    @3
    @4
    @1
    c0
    wne
    #
    @2
    @5
    @6
    @0
    cM
    cuz
    cfv
    #
    cZ
    @0
    @7
    wcel
    @0
    cz
    wcel
    @0
    @1
    wcel
    @6
    cM
    @0
    eluzelz
    @0
    uzid
    @1
    @0
    ne0i
    3syl
    rexuz3.1
    eleq2s
    wph
    vk
    @1
    r19.2z
    sylan
    @4
    @5
    @3
    @4
    wph
    wph
    vk
    @1
    cZ
    @4
    vk
    cv
    #
    @1
    wcel
    #
    @8
    cZ
    wcel
    #
    wph
    @4
    @9
    @10
    cM
    @8
    @0
    cZ
    rexuz3.1
    uztrn2
    ex
    anim1d
    reximdv2
    imp
    syldan
    rexlimiva
end
