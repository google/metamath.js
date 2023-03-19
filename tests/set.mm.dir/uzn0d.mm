include "uzidd2.mm"
include "ne0d.mm"

theorem uzn0d
  let wph: wff ph
  let cM: class M
  let cZ: class Z
  assume uzn0d.1: |- ( ph -> M e. ZZ )
  assume uzn0d.2: |- Z = ( ZZ>= ` M )


  assert |- ( ph -> Z =/= (/) )

  proof
    wph
    cZ
    cM
    wph
    cM
    cZ
    uzn0d.1
    uzn0d.2
    uzidd2
    ne0d
end
