include "wi.mm"
include "wn.mm"
include "wa.mm"
include "confun.mm"

theorem confun3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vk: setvar k
  let vx: setvar x
  assume confun3.1: |- ( ph <-> ( ch -> ps ) )
  assume confun3.2: |- ( th <-> -. ( ch -> ( ch /\ -. ch ) ) )
  assume confun3.3: |- ( ch -> ps )
  assume confun3.4: |- ( ch -> -. ( ch -> ( ch /\ -. ch ) ) )
  assume confun3.5: |- ( ( ch -> ps ) -> ( ( ch -> ps ) -> ps ) )


  assert |- ( ch -> ( -. ( ch -> ( ch /\ -. ch ) ) <-> ( ch -> ps ) ) )

  proof
    wch
    wps
    wi
    wps
    wch
    wch
    wch
    wch
    wn
    wa
    wi
    wn
    confun3.3
    confun3.3
    confun3.4
    confun3.5
    confun
end
