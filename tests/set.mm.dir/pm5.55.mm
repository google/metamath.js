include "wo.mm"
include "wb.mm"
include "biort.mm"
include "bicomd.mm"
include "wn.mm"
include "biorf.mm"
include "nsyl4.mm"
include "con1i.mm"
include "orri.mm"

theorem pm5.55
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ( ph \/ ps ) <-> ph ) \/ ( ( ph \/ ps ) <-> ps ) )

  proof
    wph
    wps
    wo
    #
    wph
    wb
    #
    @0
    wps
    wb
    #
    @2
    @1
    wph
    @1
    @2
    wph
    wph
    @0
    wph
    wps
    biort
    bicomd
    wph
    wn
    wps
    @0
    wph
    wps
    biorf
    bicomd
    nsyl4
    con1i
    orri
end
