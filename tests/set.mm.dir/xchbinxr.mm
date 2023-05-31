include "bicomi.mm"
include "xchbinx.mm"

theorem xchbinxr
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume xchbinxr.1: |- ( ph <-> -. ps )
  assume xchbinxr.2: |- ( ch <-> ps )


  assert |- ( ph <-> -. ch )

  proof
    wph
    wps
    wch
    xchbinxr.1
    wch
    wps
    xchbinxr.2
    bicomi
    xchbinx
end
