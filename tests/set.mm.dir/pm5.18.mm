include "wb.mm"
include "wn.mm"
include "pm5.501.mm"
include "con1bid.mm"
include "bitr2d.mm"
include "nbn2.mm"
include "pm2.61i.mm"

theorem pm5.18
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph <-> ps ) <-> -. ( ph <-> -. ps ) )

  proof
    wph
    wph
    wps
    wb
    #
    wph
    wps
    wn
    #
    wb
    #
    wn
    #
    wb
    wph
    @3
    wps
    @0
    wph
    wps
    @2
    wph
    @1
    pm5.501
    con1bid
    wph
    wps
    pm5.501
    bitr2d
    wph
    wn
    #
    @3
    @1
    @0
    @4
    @1
    @2
    wph
    @1
    nbn2
    con1bid
    wph
    wps
    nbn2
    bitr2d
    pm2.61i
end
