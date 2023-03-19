include "chil.mm"
include "wcel.mm"
include "ccom.mm"
include "cfv.mm"
include "hocofi.mm"
include "hocoi.mm"
include "wceq.mm"
include "ffvelrni.mm"
include "syl.mm"
include "eqtrd.mm"

theorem ho2coi
  let cA: class A
  let cR: class R
  let cS: class S
  let cT: class T
  let vx: setvar x
  assume hods.1: |- R : ~H --> ~H
  assume hods.2: |- S : ~H --> ~H
  assume hods.3: |- T : ~H --> ~H


  assert |- ( A e. ~H -> ( ( ( R o. S ) o. T ) ` A ) = ( R ` ( S ` ( T ` A ) ) ) )

  proof
    cA
    chil
    wcel
    #
    cA
    cR
    cS
    ccom
    #
    cT
    ccom
    cfv
    cA
    cT
    cfv
    #
    @1
    cfv
    #
    @2
    cS
    cfv
    cR
    cfv
    #
    cA
    @1
    cT
    cR
    cS
    hods.1
    hods.2
    hocofi
    hods.3
    hocoi
    @0
    @2
    chil
    wcel
    @3
    @4
    wceq
    chil
    chil
    cA
    cT
    hods.3
    ffvelrni
    @2
    cR
    cS
    hods.1
    hods.2
    hocoi
    syl
    eqtrd
end
