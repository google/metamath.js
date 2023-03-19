include "wi.mm"
include "wo.mm"
include "bj-curry.mm"
include "bj-orim2.mm"
include "mpi.mm"
include "pm1.2.mm"
include "syl.mm"

theorem bj-peirce
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ( ph -> ps ) -> ph ) -> ph )

  proof
    wph
    wps
    wi
    #
    wph
    wi
    #
    wph
    wph
    wo
    #
    wph
    @1
    wph
    @0
    wo
    @2
    wph
    wps
    bj-curry
    @0
    wph
    wph
    bj-orim2
    mpi
    wph
    pm1.2
    syl
end
