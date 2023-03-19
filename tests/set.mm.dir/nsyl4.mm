include "wn.mm"
include "con1i.mm"
include "syl.mm"

theorem nsyl4
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume nsyl4.1: |- ( ph -> ps )
  assume nsyl4.2: |- ( -. ph -> ch )


  assert |- ( -. ch -> ps )

  proof
    wch
    wn
    wph
    wps
    wph
    wch
    nsyl4.2
    con1i
    nsyl4.1
    syl
end
