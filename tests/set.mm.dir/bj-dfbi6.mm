include "wb.mm"
include "wo.mm"
include "wa.mm"
include "wi.mm"
include "bj-dfbi5.mm"
include "id.mm"
include "animorr.mm"
include "impbid1.mm"
include "biimp.mm"
include "impbii.mm"
include "bitri.mm"

theorem bj-dfbi6
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph <-> ps ) <-> ( ( ph \/ ps ) <-> ( ph /\ ps ) ) )

  proof
    wph
    wps
    wb
    wph
    wps
    wo
    #
    wph
    wps
    wa
    #
    wi
    #
    @0
    @1
    wb
    #
    wph
    wps
    bj-dfbi5
    @2
    @3
    @2
    @0
    @1
    @2
    id
    wph
    wps
    wph
    animorr
    impbid1
    @0
    @1
    biimp
    impbii
    bitri
end
