include "wa.mm"
include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "wral.mm"
include "wrex.mm"
include "cz.mm"
include "wcel.mm"
include "eluzel2.mm"
include "eleq2s.mm"
include "a1d.mm"
include "rexlimiv.mm"
include "adantr.mm"
include "rexuz3.mm"
include "anbi12d.mm"
include "rexanuz.mm"
include "syl6rbbr.mm"
include "bitrd.mm"
include "pm5.21nii.mm"

theorem rexanuz2
  let wph: wff ph
  let wps: wff ps
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cZ: class Z
  let vm: setvar m
  assume rexuz3.1: |- Z = ( ZZ>= ` M )

  disjoint j ps
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
  assert |- ( E. j e. Z A. k e. ( ZZ>= ` j ) ( ph /\ ps ) <-> ( E. j e. Z A. k e. ( ZZ>= ` j ) ph /\ E. j e. Z A. k e. ( ZZ>= ` j ) ps ) )

  proof
    wph
    wps
    wa
    #
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
    #
    cM
    cz
    wcel
    #
    wph
    vk
    @2
    wral
    #
    vj
    cZ
    wrex
    #
    wps
    vk
    @2
    wral
    #
    vj
    cZ
    wrex
    #
    wa
    #
    @3
    @5
    vj
    cZ
    @1
    cZ
    wcel
    #
    @5
    @3
    @5
    @1
    cM
    cuz
    cfv
    cZ
    cM
    @1
    eluzel2
    rexuz3.1
    eleq2s
    #
    a1d
    rexlimiv
    @7
    @5
    @9
    @6
    @5
    vj
    cZ
    @11
    @5
    @6
    @12
    a1d
    rexlimiv
    adantr
    @5
    @4
    @3
    vj
    cz
    wrex
    #
    @10
    @0
    vj
    vk
    cM
    cZ
    rexuz3.1
    rexuz3
    @5
    @10
    @6
    vj
    cz
    wrex
    #
    @8
    vj
    cz
    wrex
    #
    wa
    @13
    @5
    @7
    @14
    @9
    @15
    wph
    vj
    vk
    cM
    cZ
    rexuz3.1
    rexuz3
    wps
    vj
    vk
    cM
    cZ
    rexuz3.1
    rexuz3
    anbi12d
    wph
    wps
    vj
    vk
    rexanuz
    syl6rbbr
    bitrd
    pm5.21nii
end
