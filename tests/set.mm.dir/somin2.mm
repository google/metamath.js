include "wor.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cif.mm"
include "cid.mm"
include "cun.mm"
include "somincom.mm"
include "somin1.mm"
include "ancom2s.mm"
include "eqbrtrd.mm"

theorem somin2
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X


  assert |- ( ( R Or X /\ ( A e. X /\ B e. X ) ) -> if ( A R B , A , B ) ( R u. _I ) B )

  proof
    cX
    cR
    wor
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    wa
    wa
    cA
    cB
    cR
    wbr
    cA
    cB
    cif
    cB
    cA
    cR
    wbr
    cB
    cA
    cif
    #
    cB
    cR
    cid
    cun
    #
    cA
    cB
    cR
    cX
    somincom
    @0
    @2
    @1
    @3
    cB
    @4
    wbr
    cB
    cA
    cR
    cX
    somin1
    ancom2s
    eqbrtrd
end
