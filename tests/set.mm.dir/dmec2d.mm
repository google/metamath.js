include "cdm.mm"
include "eqidd.mm"
include "dmecd.mm"

theorem dmec2d
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cR: class R
  assume dmec2d.1: |- ( ph -> [ B ] R = [ C ] R )


  assert |- ( ph -> ( B e. dom R <-> C e. dom R ) )

  proof
    wph
    cR
    cdm
    #
    cB
    cC
    cR
    wph
    @0
    eqidd
    dmec2d.1
    dmecd
end
