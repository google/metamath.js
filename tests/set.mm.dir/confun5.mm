include "wb.mm"
include "wi.mm"
include "wn.mm"
include "wa.mm"
include "ax-mp.mm"
include "atnaiana.mm"
include "bicom1.mm"
include "biimpi.mm"
include "2th.mm"
include "ax-1.mm"

theorem confun5
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vk: setvar k
  let vx: setvar x
  assume confun5.1: |- ph
  assume confun5.2: |- ( ( ph -> ps ) -> ps )
  assume confun5.3: |- ( ps -> ( ph -> ch ) )
  assume confun5.4: |- ( ( ch -> th ) -> ( ( ph -> th ) <-> ps ) )
  assume confun5.5: |- ( ta <-> ( ch -> th ) )
  assume confun5.6: |- ( et <-> -. ( ch -> ( ch /\ -. ch ) ) )
  assume confun5.7: |- ps
  assume confun5.8: |- ( ch -> th )


  assert |- ( ch -> ( et <-> ta ) )

  proof
    wet
    wta
    wb
    #
    wch
    @0
    wi
    wet
    wta
    wch
    wch
    wch
    wn
    wa
    wi
    wn
    #
    wet
    wch
    wph
    wch
    confun5.1
    wps
    wph
    wch
    wi
    confun5.7
    confun5.3
    ax-mp
    ax-mp
    atnaiana
    @1
    wet
    wet
    @1
    wb
    @1
    wet
    wb
    confun5.6
    wet
    @1
    bicom1
    ax-mp
    biimpi
    ax-mp
    wch
    wth
    wi
    #
    wta
    confun5.8
    @2
    wta
    wta
    @2
    wb
    @2
    wta
    wb
    confun5.5
    wta
    @2
    bicom1
    ax-mp
    biimpi
    ax-mp
    2th
    @0
    wch
    ax-1
    ax-mp
end
