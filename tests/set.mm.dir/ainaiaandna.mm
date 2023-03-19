include "wn.mm"
include "wa.mm"
include "wi.mm"
include "atnaiana.mm"
include "a1i.mm"

theorem ainaiaandna
  let wph: wff ph
  let vk: setvar k
  let vx: setvar x
  assume ainaiaandna.1: |- ph


  assert |- ( ph -> -. ( ph -> ( ph /\ -. ph ) ) )

  proof
    wph
    wph
    wph
    wn
    wa
    wi
    wn
    wph
    wph
    ainaiaandna.1
    atnaiana
    a1i
end
