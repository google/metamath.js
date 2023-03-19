include "cz.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cv.mm"
include "crab.mm"
include "peano2z.mm"
include "ad2antrl.mm"
include "cr.mm"
include "wi.mm"
include "zre.mm"
include "lep1.mm"
include "adantl.mm"
include "peano2re.mm"
include "ancli.mm"
include "letr.mm"
include "3expb.mm"
include "sylan2.mm"
include "mpan2d.mm"
include "syl2an.mm"
include "impr.mm"
include "jca.mm"
include "breq2.mm"
include "elrab.mm"
include "anbi2i.mm"
include "3imtr4i.mm"

theorem peano2uz2
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( A e. ZZ /\ B e. { x e. ZZ | A <_ x } ) -> ( B + 1 ) e. { x e. ZZ | A <_ x } )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    wa
    #
    wa
    #
    cB
    c1
    caddc
    co
    #
    cz
    wcel
    #
    cA
    @5
    cle
    wbr
    #
    wa
    @0
    cB
    cA
    vx
    cv
    #
    cle
    wbr
    #
    vx
    cz
    crab
    #
    wcel
    #
    wa
    @5
    @10
    wcel
    @4
    @6
    @7
    @1
    @6
    @0
    @2
    cB
    peano2z
    ad2antrl
    @0
    @1
    @2
    @7
    @0
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @2
    @7
    wi
    @1
    cA
    zre
    cB
    zre
    @12
    @13
    wa
    @2
    cB
    @5
    cle
    wbr
    #
    @7
    @13
    @14
    @12
    cB
    lep1
    adantl
    @13
    @12
    @13
    @5
    cr
    wcel
    #
    wa
    @2
    @14
    wa
    @7
    wi
    #
    @13
    @15
    cB
    peano2re
    ancli
    @12
    @13
    @15
    @16
    cA
    cB
    @5
    letr
    3expb
    sylan2
    mpan2d
    syl2an
    impr
    jca
    @11
    @3
    @0
    @9
    @2
    vx
    cB
    cz
    @8
    cB
    cA
    cle
    breq2
    elrab
    anbi2i
    @9
    @7
    vx
    @5
    cz
    @8
    @5
    cA
    cle
    breq2
    elrab
    3imtr4i
end
