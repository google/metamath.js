include "cr.mm"
include "wss.mm"
include "covol.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "cin.mm"
include "cdif.mm"
include "caddc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "cvol.mm"
include "cdm.mm"
include "simpl.mm"
include "elpwi.mm"
include "inss2.mm"
include "ovolssnul.mm"
include "mp3an1.mm"
include "adantr.mm"
include "oveq1d.mm"
include "difss.mm"
include "ovolsscl.mm"
include "adantl.mm"
include "recnd.mm"
include "addid2d.mm"
include "eqtrd.mm"
include "simprl.mm"
include "ovolss.mm"
include "sylancr.mm"
include "eqbrtrd.mm"
include "expr.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "ismbl2.mm"
include "sylanbrc.mm"

theorem nulmbl
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B


  assert |- ( ( A C_ RR /\ ( vol* ` A ) = 0 ) -> A e. dom vol )

  proof
    cA
    cr
    wss
    #
    cA
    covol
    cfv
    cc0
    wceq
    #
    wa
    #
    @0
    vx
    cv
    #
    covol
    cfv
    #
    cr
    wcel
    #
    @3
    cA
    cin
    #
    covol
    cfv
    #
    @3
    cA
    cdif
    #
    covol
    cfv
    #
    caddc
    co
    #
    @4
    cle
    wbr
    #
    wi
    #
    vx
    cr
    cpw
    #
    wral
    cA
    cvol
    cdm
    wcel
    @0
    @1
    simpl
    @2
    @12
    vx
    @13
    @3
    @13
    wcel
    @2
    @3
    cr
    wss
    #
    @12
    @3
    cr
    elpwi
    @2
    @14
    @5
    @11
    @2
    @14
    @5
    wa
    #
    wa
    #
    @10
    @9
    @4
    cle
    @16
    @10
    cc0
    @9
    caddc
    co
    @9
    @16
    @7
    cc0
    @9
    caddc
    @2
    @7
    cc0
    wceq
    #
    @15
    @6
    cA
    wss
    @0
    @1
    @17
    @3
    cA
    inss2
    @6
    cA
    ovolssnul
    mp3an1
    adantr
    oveq1d
    @16
    @9
    @16
    @9
    @15
    @9
    cr
    wcel
    #
    @2
    @8
    @3
    wss
    #
    @14
    @5
    @18
    @3
    cA
    difss
    #
    @8
    @3
    ovolsscl
    mp3an1
    adantl
    recnd
    addid2d
    eqtrd
    @16
    @19
    @14
    @9
    @4
    cle
    wbr
    @20
    @2
    @14
    @5
    simprl
    @8
    @3
    ovolss
    sylancr
    eqbrtrd
    expr
    sylan2
    ralrimiva
    vx
    cA
    ismbl2
    sylanbrc
end
