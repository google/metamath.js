include "wi.mm"
include "id.mm"
include "exiftru.mm"
include "19.35i.mm"

theorem 19.2
  param wph: wff ph
  param vx: setvar x


  assert |- ( A. x ph -> E. x ph )

  proof
    wph
    wph
    vx
    wph
    wph
    wi
    vx
    wph
    id
    exiftru
    19.35i
end
