include "wnan.mm"
include "wn.mm"
include "wb.mm"
include "nannot.mm"
include "bicomi.mm"
include "nanbi.mm"
include "mpbi.mm"

theorem nic-dfneg
  let wph: wff ph


  assert |- ( ( ( ph -/\ ph ) -/\ -. ph ) -/\ ( ( ( ph -/\ ph ) -/\ ( ph -/\ ph ) ) -/\ ( -. ph -/\ -. ph ) ) )

  proof
    wph
    wph
    wnan
    #
    wph
    wn
    #
    wb
    @0
    @1
    wnan
    @0
    @0
    wnan
    @1
    @1
    wnan
    wnan
    wnan
    @1
    @0
    wph
    nannot
    bicomi
    @0
    @1
    nanbi
    mpbi
end
