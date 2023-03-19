include "cz.mm"
include "wcel.mm"
include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "id.mm"
include "rgen.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "raleqdv.mm"
include "rspcev.mm"
include "mpan2.mm"
include "biantrurd.mm"
include "uztrn2.mm"
include "a1d.mm"
include "ancrd.mm"
include "ralimdva.mm"
include "eluzelz.mm"
include "eleq2s.mm"
include "jctild.mm"
include "imp.mm"
include "uzid.mm"
include "simpl.mm"
include "ralimi.mm"
include "eleq1.mm"
include "rspcva.mm"
include "syl2an.mm"
include "simpr.mm"
include "adantl.mm"
include "jca.mm"
include "impbii.mm"
include "rexbii2.mm"
include "rexanuz.mm"
include "bitr2i.mm"
include "syl6rbb.mm"

theorem rexuz3
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
  assert |- ( M e. ZZ -> ( E. j e. Z A. k e. ( ZZ>= ` j ) ph <-> E. j e. ZZ A. k e. ( ZZ>= ` j ) ph ) )

  proof
    cM
    cz
    wcel
    #
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
    vj
    cz
    wrex
    #
    vk
    cv
    #
    cZ
    wcel
    #
    vk
    @2
    wral
    #
    vj
    cz
    wrex
    #
    @4
    wa
    #
    @3
    vj
    cZ
    wrex
    #
    @0
    @8
    @4
    @0
    @6
    vk
    cZ
    wral
    #
    @8
    @6
    vk
    cZ
    @6
    id
    rgen
    @7
    @11
    vj
    cM
    cz
    @1
    cM
    wceq
    #
    @6
    vk
    @2
    cZ
    @12
    @2
    cM
    cuz
    cfv
    #
    cZ
    @1
    cM
    cuz
    fveq2
    rexuz3.1
    syl6eqr
    raleqdv
    rspcev
    mpan2
    biantrurd
    @10
    @6
    wph
    wa
    #
    vk
    @2
    wral
    #
    vj
    cz
    wrex
    @9
    @3
    @15
    vj
    cZ
    cz
    @1
    cZ
    wcel
    #
    @3
    wa
    @1
    cz
    wcel
    #
    @15
    wa
    #
    @16
    @3
    @18
    @16
    @3
    @15
    @17
    @16
    wph
    @14
    vk
    @2
    @16
    @5
    @2
    wcel
    wa
    #
    wph
    @6
    @19
    @6
    wph
    cM
    @5
    @1
    cZ
    rexuz3.1
    uztrn2
    a1d
    ancrd
    ralimdva
    @17
    @1
    @13
    cZ
    cM
    @1
    eluzelz
    rexuz3.1
    eleq2s
    jctild
    imp
    @18
    @16
    @3
    @17
    @1
    @2
    wcel
    @7
    @16
    @15
    @1
    uzid
    @14
    @6
    vk
    @2
    @6
    wph
    simpl
    ralimi
    @6
    @16
    vk
    @1
    @2
    @5
    @1
    cZ
    eleq1
    rspcva
    syl2an
    @15
    @3
    @17
    @14
    wph
    vk
    @2
    @6
    wph
    simpr
    ralimi
    adantl
    jca
    impbii
    rexbii2
    @6
    wph
    vj
    vk
    rexanuz
    bitr2i
    syl6rbb
end
