include "wi.mm"
include "wn.mm"
include "wl-con1i.mm"
include "wl-imim2i.mm"
include "wl-syl5.mm"
include "wl-pm2.18d.mm"

theorem wl-ja
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume wl-ja.1: |- ( -. ph -> ch )
  assume wl-ja.2: |- ( ps -> ch )


  assert |- ( ( ph -> ps ) -> ch )

  proof
    wph
    wps
    wi
    #
    wch
    wch
    wn
    wph
    @0
    wch
    wph
    wch
    wl-ja.1
    wl-con1i
    wps
    wch
    wph
    wl-ja.2
    wl-imim2i
    wl-syl5
    wl-pm2.18d
end
