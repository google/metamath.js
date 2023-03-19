include "wral.mm"
include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "wrex.mm"
include "wa.mm"
include "wcel.mm"
include "wi.mm"
include "uztrn2.mm"
include "ex.mm"
include "pm3.2.mm"
include "a1i.mm"
include "imim12d.mm"
include "ralimdv2.mm"
include "impcom.mm"
include "ralim.mm"
include "syl.mm"
include "reximdva.mm"
include "imp.mm"

theorem r19.29uz
  let wph: wff ph
  let wps: wff ps
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
  assert |- ( ( A. k e. Z ph /\ E. j e. Z A. k e. ( ZZ>= ` j ) ps ) -> E. j e. Z A. k e. ( ZZ>= ` j ) ( ph /\ ps ) )

  proof
    wph
    vk
    cZ
    wral
    #
    wps
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cZ
    wrex
    wph
    wps
    wa
    #
    vk
    @2
    wral
    #
    vj
    cZ
    wrex
    @0
    @3
    @5
    vj
    cZ
    @0
    @1
    cZ
    wcel
    #
    wa
    wps
    @4
    wi
    #
    vk
    @2
    wral
    #
    @3
    @5
    wi
    @6
    @0
    @8
    @6
    wph
    @7
    vk
    cZ
    @2
    @6
    vk
    cv
    #
    @2
    wcel
    #
    @9
    cZ
    wcel
    #
    wph
    @7
    @6
    @10
    @11
    cM
    @9
    @1
    cZ
    rexuz3.1
    uztrn2
    ex
    wph
    @7
    wi
    @6
    wph
    wps
    pm3.2
    a1i
    imim12d
    ralimdv2
    impcom
    wps
    @4
    vk
    @2
    ralim
    syl
    reximdva
    imp
end
