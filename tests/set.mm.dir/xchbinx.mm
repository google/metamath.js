include "wn.mm"
include "notbii.mm"
include "bitri.mm"

theorem xchbinx
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume xchbinx.1: |- ( ph <-> -. ps )
  assume xchbinx.2: |- ( ps <-> ch )


  assert |- ( ph <-> -. ch )

  proof
    wph
    wps
    wn
    wch
    wn
    xchbinx.1
    wps
    wch
    xchbinx.2
    notbii
    bitri
end
