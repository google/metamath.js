include "wn.mm"
include "pm2.65da.mm"
include "notnotrd.mm"

theorem condan
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume condan.1: |- ( ( ph /\ -. ps ) -> ch )
  assume condan.2: |- ( ( ph /\ -. ps ) -> -. ch )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wph
    wps
    wn
    wch
    condan.1
    condan.2
    pm2.65da
    notnotrd
end
