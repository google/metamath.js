include "wn.mm"
include "wa.mm"
include "wi.mm"
include "bitru.mm"
include "pm3.24.mm"
include "bifal.mm"
include "aifftbifffaibif.mm"
include "aisfina.mm"

theorem atnaiana
  let wph: wff ph
  let vk: setvar k
  let vx: setvar x
  assume atnaiana.1: |- ph


  assert |- -. ( ph -> ( ph /\ -. ph ) )

  proof
    wph
    wph
    wph
    wn
    wa
    #
    wi
    wph
    @0
    wph
    atnaiana.1
    bitru
    @0
    wph
    pm3.24
    bifal
    aifftbifffaibif
    aisfina
end
