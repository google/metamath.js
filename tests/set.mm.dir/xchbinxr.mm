include "bicomi.mm"
include "xchbinx.mm"

theorem xchbinxr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
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
