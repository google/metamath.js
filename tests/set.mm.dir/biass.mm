include "wb.mm"
include "pm5.501.mm"
include "bibi1d.mm"
include "bitr3d.mm"
include "wn.mm"
include "nbbn.mm"
include "nbn2.mm"
include "syl5bbr.mm"
include "pm2.61i.mm"

theorem biass
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph <-> ps ) <-> ch ) <-> ( ph <-> ( ps <-> ch ) ) )

  proof
    wph
    wph
    wps
    wb
    #
    wch
    wb
    #
    wph
    wps
    wch
    wb
    #
    wb
    #
    wb
    wph
    @2
    @1
    @3
    wph
    wps
    @0
    wch
    wph
    wps
    pm5.501
    bibi1d
    wph
    @2
    pm5.501
    bitr3d
    wph
    wn
    #
    @2
    wn
    #
    @1
    @3
    @5
    wps
    wn
    #
    wch
    wb
    @4
    @1
    wps
    wch
    nbbn
    @4
    @6
    @0
    wch
    wph
    wps
    nbn2
    bibi1d
    syl5bbr
    wph
    @2
    nbn2
    bitr3d
    pm2.61i
end
