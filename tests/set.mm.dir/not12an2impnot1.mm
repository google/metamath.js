include "wa.mm"
include "wn.mm"
include "pm3.21.mm"
include "con3rr3.mm"
include "imp.mm"

theorem not12an2impnot1
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( -. ( ph /\ ps ) /\ ps ) -> -. ph )

  proof
    wph
    wps
    wa
    #
    wn
    wps
    wph
    wn
    wps
    wph
    @0
    wps
    wph
    pm3.21
    con3rr3
    imp
end
