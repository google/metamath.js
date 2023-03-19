include "cv.mm"
include "cprod.mm"
include "cabs.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wral.mm"
include "fproddvdsd.mm"
include "wcel.mm"
include "wa.mm"
include "cz.mm"
include "wb.mm"
include "sselda.mm"
include "fprodzcl.mm"
include "adantr.mm"
include "dvdsabsb.mm"
include "syl2anc.mm"
include "biimpd.mm"
include "ralimdva.mm"
include "mpd.mm"
include "breq2i.mm"
include "ralbii.mm"
include "sylibr.mm"

theorem absproddvds
  let wph: wff ph
  let vz: setvar z
  let cP: class P
  let vm: setvar m
  let cZ: class Z
  assume absproddvds.s: |- ( ph -> Z C_ ZZ )
  assume absproddvds.f: |- ( ph -> Z e. Fin )
  assume absproddvds.p: |- P = ( abs ` prod_ z e. Z z )

  disjoint Z z
  disjoint m ph
  disjoint ph z
  disjoint m z
  assert |- ( ph -> A. m e. Z m || P )

  proof
    wph
    vm
    cv
    #
    cZ
    vz
    cv
    #
    vz
    cprod
    #
    cabs
    cfv
    #
    cdvds
    wbr
    #
    vm
    cZ
    wral
    #
    @0
    cP
    cdvds
    wbr
    #
    vm
    cZ
    wral
    wph
    @0
    @2
    cdvds
    wbr
    #
    vm
    cZ
    wral
    @5
    wph
    vm
    cZ
    vz
    absproddvds.f
    absproddvds.s
    fproddvdsd
    wph
    @7
    @4
    vm
    cZ
    wph
    @0
    cZ
    wcel
    #
    wa
    #
    @7
    @4
    @9
    @0
    cz
    wcel
    @2
    cz
    wcel
    #
    @7
    @4
    wb
    wph
    cZ
    cz
    @0
    absproddvds.s
    sselda
    wph
    @10
    @8
    wph
    cZ
    @1
    vz
    absproddvds.f
    wph
    cZ
    cz
    @1
    absproddvds.s
    sselda
    fprodzcl
    adantr
    @0
    @2
    dvdsabsb
    syl2anc
    biimpd
    ralimdva
    mpd
    @6
    @4
    vm
    cZ
    cP
    @3
    @0
    cdvds
    absproddvds.p
    breq2i
    ralbii
    sylibr
end
