include "cv.mm"
include "wbr.mm"
include "copab.mm"
include "cop.mm"
include "wcel.mm"
include "breqi.mm"
include "df-br.mm"
include "opabid.mm"
include "3bitri.mm"

theorem brabidga
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  assume brabidga.1: |- R = { <. x , y >. | ph }


  assert |- ( x R y <-> ph )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    @0
    @1
    wph
    vx
    vy
    copab
    #
    wbr
    @0
    @1
    cop
    @2
    wcel
    wph
    @0
    @1
    cR
    @2
    brabidga.1
    breqi
    @0
    @1
    @2
    df-br
    wph
    vx
    vy
    opabid
    3bitri
end
