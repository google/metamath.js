include "cxp.mm"
include "cdif.mm"
include "cun.mm"
include "wss.mm"
include "wrel.mm"
include "difss.mm"
include "relxp.mm"
include "relss.mm"
include "mp2.mm"
include "relun.mm"
include "mpbir2an.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "ianor.mm"
include "anbi2i.mm"
include "andi.mm"
include "bitri.mm"
include "opelxp.mm"
include "notbii.mm"
include "anbi12i.mm"
include "eldif.mm"
include "anbi1i.mm"
include "an32.mm"
include "anass.mm"
include "3bitr4i.mm"
include "orbi12i.mm"
include "elun.mm"
include "eqrelriiv.mm"

theorem difxp
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( C X. D ) \ ( A X. B ) ) = ( ( ( C \ A ) X. D ) u. ( C X. ( D \ B ) ) )

  proof
    vx
    vy
    cC
    cD
    cxp
    #
    cA
    cB
    cxp
    #
    cdif
    #
    cC
    cA
    cdif
    #
    cD
    cxp
    #
    cC
    cD
    cB
    cdif
    #
    cxp
    #
    cun
    #
    @2
    @0
    wss
    @0
    wrel
    @2
    wrel
    @0
    @1
    difss
    cC
    cD
    relxp
    @2
    @0
    relss
    mp2
    @7
    wrel
    @4
    wrel
    @6
    wrel
    @3
    cD
    relxp
    cC
    @5
    relxp
    @4
    @6
    relun
    mpbir2an
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    @0
    wcel
    #
    @10
    @1
    wcel
    #
    wn
    #
    wa
    #
    @10
    @4
    wcel
    #
    @10
    @6
    wcel
    #
    wo
    #
    @10
    @2
    wcel
    @10
    @7
    wcel
    @8
    cC
    wcel
    #
    @9
    cD
    wcel
    #
    wa
    #
    @8
    cA
    wcel
    #
    @9
    cB
    wcel
    #
    wa
    #
    wn
    #
    wa
    #
    @20
    @21
    wn
    #
    wa
    #
    @20
    @22
    wn
    #
    wa
    #
    wo
    #
    @14
    @17
    @25
    @20
    @26
    @28
    wo
    #
    wa
    @30
    @24
    @31
    @20
    @21
    @22
    ianor
    anbi2i
    @20
    @26
    @28
    andi
    bitri
    @11
    @20
    @13
    @24
    @8
    @9
    cC
    cD
    opelxp
    @12
    @23
    @8
    @9
    cA
    cB
    opelxp
    notbii
    anbi12i
    @15
    @27
    @16
    @29
    @15
    @8
    @3
    wcel
    #
    @19
    wa
    #
    @27
    @8
    @9
    @3
    cD
    opelxp
    @33
    @18
    @26
    wa
    #
    @19
    wa
    @27
    @32
    @34
    @19
    @8
    cC
    cA
    eldif
    anbi1i
    @18
    @26
    @19
    an32
    bitri
    bitri
    @18
    @9
    @5
    wcel
    #
    wa
    @18
    @19
    @28
    wa
    #
    wa
    @16
    @29
    @35
    @36
    @18
    @9
    cD
    cB
    eldif
    anbi2i
    @8
    @9
    cC
    @5
    opelxp
    @18
    @19
    @28
    anass
    3bitr4i
    orbi12i
    3bitr4i
    @10
    @0
    @1
    eldif
    @10
    @4
    @6
    elun
    3bitr4i
    eqrelriiv
end
