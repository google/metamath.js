include "wb.mm"
include "wi.mm"
include "idn2.mm"
include "idn1.mm"
include "idn3.mm"
include "biimpr.mm"
include "imim1d.mm"
include "e13.mm"
include "biimp.mm"
include "imim2d.mm"
include "e23.mm"
include "in3.mm"
include "impbi.mm"
include "e22.mm"
include "in2.mm"
include "in1.mm"

theorem imbi12VD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph <-> ps ) -> ( ( ch <-> th ) -> ( ( ph -> ch ) <-> ( ps -> th ) ) ) )

  proof
    wph
    wps
    wb
    #
    wch
    wth
    wb
    #
    wph
    wch
    wi
    #
    wps
    wth
    wi
    #
    wb
    #
    wi
    @0
    @1
    @4
    @0
    @1
    @2
    @3
    wi
    @3
    @2
    wi
    @4
    @0
    @1
    @2
    @3
    @0
    @1
    @1
    @2
    wps
    wch
    wi
    #
    @3
    @0
    @1
    idn2
    #
    @0
    @0
    @1
    @2
    @2
    @5
    @0
    idn1
    #
    @0
    @1
    @2
    idn3
    @0
    wps
    wph
    wch
    wph
    wps
    biimpr
    imim1d
    e13
    @1
    wch
    wth
    wps
    wch
    wth
    biimp
    imim2d
    e23
    in3
    @0
    @1
    @3
    @2
    @0
    @1
    @1
    @3
    wph
    wth
    wi
    #
    @2
    @6
    @0
    @0
    @1
    @3
    @3
    @8
    @7
    @0
    @1
    @3
    idn3
    @0
    wph
    wps
    wth
    wph
    wps
    biimp
    imim1d
    e13
    @1
    wth
    wch
    wph
    wch
    wth
    biimpr
    imim2d
    e23
    in3
    @2
    @3
    impbi
    e22
    in2
    in1
end
