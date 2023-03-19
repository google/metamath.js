include "topnpropd.mm"
include "tpspropd.mm"

theorem tpsprop2d
  let wph: wff ph
  let cK: class K
  let cL: class L
  assume tpsprop2d.1: |- ( ph -> ( Base ` K ) = ( Base ` L ) )
  assume tpsprop2d.2: |- ( ph -> ( TopSet ` K ) = ( TopSet ` L ) )


  assert |- ( ph -> ( K e. TopSp <-> L e. TopSp ) )

  proof
    wph
    cK
    cL
    tpsprop2d.1
    wph
    cK
    cL
    tpsprop2d.1
    tpsprop2d.2
    topnpropd
    tpspropd
end
