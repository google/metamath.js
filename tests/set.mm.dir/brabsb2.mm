include "copab.mm"
include "wceq.mm"
include "cv.mm"
include "wbr.mm"
include "cop.mm"
include "wcel.mm"
include "wsb.mm"
include "breq.mm"
include "df-br.mm"
include "syl6bb.mm"
include "opelopabsbALT.mm"

theorem brabsb2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cR: class R

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint w x
  disjoint w y
  assert |- ( R = { <. x , y >. | ph } -> ( z R w <-> [ w / y ] [ z / x ] ph ) )

  proof
    cR
    wph
    vx
    vy
    copab
    #
    wceq
    #
    vz
    cv
    #
    vw
    cv
    #
    cR
    wbr
    #
    @2
    @3
    cop
    @0
    wcel
    #
    wph
    vx
    vz
    wsb
    vy
    vw
    wsb
    @1
    @4
    @2
    @3
    @0
    wbr
    @5
    @2
    @3
    cR
    @0
    breq
    @2
    @3
    @0
    df-br
    syl6bb
    wph
    vx
    vy
    vz
    vw
    opelopabsbALT
    syl6bb
end
