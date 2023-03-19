include "wtru.mm"
include "wn.mm"
include "wo.mm"
include "orc.mm"
include "wb.mm"
include "tru.mm"
include "biid.mm"
include "2th.mm"
include "exmid.mm"
include "a1i.mm"
include "biidd.mm"
include "impbii.mm"
include "bitri.mm"
include "sylibr.mm"
include "mpancom.mm"

theorem uunT1
  let wph: wff ph
  let wps: wff ps
  assume uunT1.1: |- ( ( T. /\ ph ) -> ps )


  assert |- ( ph -> ps )

  proof
    wtru
    wph
    wps
    wph
    wph
    wph
    wn
    #
    wo
    #
    wtru
    wph
    @0
    orc
    wtru
    wph
    wph
    wb
    #
    @1
    wtru
    @2
    tru
    wph
    biid
    2th
    @2
    @1
    @1
    @2
    wph
    exmid
    a1i
    @1
    wph
    biidd
    impbii
    bitri
    sylibr
    uunT1.1
    mpancom
end
