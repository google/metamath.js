include "weq.mm"
include "wsb.mm"
include "equsb3.mm"
include "biimpi.mm"
include "imim2i.mm"

theorem frege55lem1b
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint y z
  assert |- ( ( ph -> [ x / y ] y = z ) -> ( ph -> x = z ) )

  proof
    vy
    vz
    weq
    vy
    vx
    wsb
    #
    vx
    vz
    weq
    #
    wph
    @0
    @1
    vx
    vy
    vz
    equsb3
    biimpi
    imim2i
end
