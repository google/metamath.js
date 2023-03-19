include "bicomi.mm"
include "xchnxbi.mm"

theorem xchnxbir
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume xchnxbir.1: |- ( -. ph <-> ps )
  assume xchnxbir.2: |- ( ch <-> ph )


  assert |- ( -. ch <-> ps )

  proof
    wph
    wps
    wch
    xchnxbir.1
    wch
    wph
    xchnxbir.2
    bicomi
    xchnxbi
end
