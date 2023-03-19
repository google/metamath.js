include "wi.mm"
include "wn.mm"
include "wa.mm"
include "aistia.mm"
include "aisfina.mm"
include "pm3.2i.mm"
include "annim.mm"
include "biimpi.mm"
include "ax-mp.mm"
include "bifal.mm"

theorem aifftbifffaibif
  let wph: wff ph
  let wps: wff ps
  let vk: setvar k
  let vx: setvar x
  assume aifftbifffaibif.1: |- ( ph <-> T. )
  assume aifftbifffaibif.2: |- ( ps <-> F. )


  assert |- ( ( ph -> ps ) <-> F. )

  proof
    wph
    wps
    wi
    #
    wph
    wps
    wn
    #
    wa
    #
    @0
    wn
    #
    wph
    @1
    wph
    aifftbifffaibif.1
    aistia
    wps
    aifftbifffaibif.2
    aisfina
    pm3.2i
    @2
    @3
    wph
    wps
    annim
    biimpi
    ax-mp
    bifal
end
