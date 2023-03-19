include "chos.mm"
include "co.mm"
include "ccom.mm"
include "wceq.mm"
include "cpjh.mm"
include "cfv.mm"
include "coeq2.mm"
include "hocofi.mm"
include "pjsdii.mm"
include "syl6eq.mm"
include "coass.mm"
include "oveq12i.mm"
include "3eqtr4g.mm"

theorem pjsdi2i
  let cR: class R
  let cS: class S
  let cT: class T
  let cH: class H
  assume pjsdi2.1: |- H e. CH
  assume pjsdi2.2: |- R : ~H --> ~H
  assume pjsdi2.3: |- S : ~H --> ~H
  assume pjsdi2.4: |- T : ~H --> ~H


  assert |- ( ( R o. ( S +op T ) ) = ( ( R o. S ) +op ( R o. T ) ) -> ( ( ( projh ` H ) o. R ) o. ( S +op T ) ) = ( ( ( ( projh ` H ) o. R ) o. S ) +op ( ( ( projh ` H ) o. R ) o. T ) ) )

  proof
    cR
    cS
    cT
    chos
    co
    #
    ccom
    #
    cR
    cS
    ccom
    #
    cR
    cT
    ccom
    #
    chos
    co
    #
    wceq
    #
    cH
    cpjh
    cfv
    #
    @1
    ccom
    #
    @6
    @2
    ccom
    #
    @6
    @3
    ccom
    #
    chos
    co
    #
    @6
    cR
    ccom
    #
    @0
    ccom
    @11
    cS
    ccom
    #
    @11
    cT
    ccom
    #
    chos
    co
    @5
    @7
    @6
    @4
    ccom
    @10
    @1
    @4
    @6
    coeq2
    @2
    @3
    cH
    pjsdi2.1
    cR
    cS
    pjsdi2.2
    pjsdi2.3
    hocofi
    cR
    cT
    pjsdi2.2
    pjsdi2.4
    hocofi
    pjsdii
    syl6eq
    @6
    cR
    @0
    coass
    @12
    @8
    @13
    @9
    chos
    @6
    cR
    cS
    coass
    @6
    cR
    cT
    coass
    oveq12i
    3eqtr4g
end
