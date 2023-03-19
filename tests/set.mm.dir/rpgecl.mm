include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cc0.mm"
include "clt.mm"
include "simp2.mm"
include "0red.mm"
include "rpre.mm"
include "3ad2ant1.mm"
include "rpgt0.mm"
include "simp3.mm"
include "ltletrd.mm"
include "elrp.mm"
include "sylanbrc.mm"

theorem rpgecl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR+ /\ B e. RR /\ A <_ B ) -> B e. RR+ )

  proof
    cA
    crp
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    w3a
    #
    @1
    cc0
    cB
    clt
    wbr
    cB
    crp
    wcel
    @0
    @1
    @2
    simp2
    #
    @3
    cc0
    cA
    cB
    @3
    0red
    @0
    @1
    cA
    cr
    wcel
    @2
    cA
    rpre
    3ad2ant1
    @4
    @0
    @1
    cc0
    cA
    clt
    wbr
    @2
    cA
    rpgt0
    3ad2ant1
    @0
    @1
    @2
    simp3
    ltletrd
    cB
    elrp
    sylanbrc
end
