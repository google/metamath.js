include "con0.mm"
include "wcel.mm"
include "cale.mm"
include "cfv.mm"
include "ccrd.mm"
include "wceq.mm"
include "cv.mm"
include "c0.mm"
include "csuc.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "com.mm"
include "cardom.mm"
include "aleph0.mm"
include "fveq2i.mm"
include "3eqtr4i.mm"
include "char.mm"
include "harcard.mm"
include "alephsuc.mm"
include "3eqtr4a.mm"
include "a1d.mm"
include "wlim.mm"
include "wral.mm"
include "wa.mm"
include "ciun.mm"
include "cvv.mm"
include "wi.mm"
include "vex.mm"
include "cardiun.mm"
include "ax-mp.mm"
include "adantl.mm"
include "alephlim.mm"
include "mpan.mm"
include "adantr.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "tfinds.mm"
include "wn.mm"
include "card0.mm"
include "cdm.mm"
include "wfn.mm"
include "alephfnon.mm"
include "fndm.mm"
include "eleq2i.mm"
include "ndmfv.mm"
include "sylnbir.mm"
include "pm2.61i.mm"

theorem alephcard
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( card ` ( aleph ` A ) ) = ( aleph ` A )

  proof
    cA
    con0
    wcel
    #
    cA
    cale
    cfv
    #
    ccrd
    cfv
    #
    @1
    wceq
    #
    vx
    cv
    #
    cale
    cfv
    #
    ccrd
    cfv
    #
    @5
    wceq
    #
    c0
    cale
    cfv
    #
    ccrd
    cfv
    #
    @8
    wceq
    vy
    cv
    #
    cale
    cfv
    #
    ccrd
    cfv
    #
    @11
    wceq
    #
    @10
    csuc
    #
    cale
    cfv
    #
    ccrd
    cfv
    #
    @15
    wceq
    #
    @3
    vx
    vy
    cA
    @4
    c0
    wceq
    #
    @6
    @9
    @5
    @8
    @18
    @5
    @8
    ccrd
    @4
    c0
    cale
    fveq2
    #
    fveq2d
    @19
    eqeq12d
    @4
    @10
    wceq
    #
    @6
    @12
    @5
    @11
    @20
    @5
    @11
    ccrd
    @4
    @10
    cale
    fveq2
    #
    fveq2d
    @21
    eqeq12d
    @4
    @14
    wceq
    #
    @6
    @16
    @5
    @15
    @22
    @5
    @15
    ccrd
    @4
    @14
    cale
    fveq2
    #
    fveq2d
    @23
    eqeq12d
    @4
    cA
    wceq
    #
    @6
    @2
    @5
    @1
    @24
    @5
    @1
    ccrd
    @4
    cA
    cale
    fveq2
    #
    fveq2d
    @25
    eqeq12d
    com
    ccrd
    cfv
    com
    @9
    @8
    cardom
    @8
    com
    ccrd
    aleph0
    fveq2i
    aleph0
    3eqtr4i
    @10
    con0
    wcel
    #
    @17
    @13
    @26
    @11
    char
    cfv
    #
    ccrd
    cfv
    @27
    @16
    @15
    @11
    harcard
    @26
    @15
    @27
    ccrd
    @10
    alephsuc
    #
    fveq2d
    @28
    3eqtr4a
    a1d
    @4
    wlim
    #
    @13
    vy
    @4
    wral
    #
    @7
    @29
    @30
    wa
    #
    vy
    @4
    @11
    ciun
    #
    ccrd
    cfv
    #
    @32
    @6
    @5
    @30
    @33
    @32
    wceq
    #
    @29
    @4
    cvv
    wcel
    #
    @30
    @34
    wi
    vx
    vex
    #
    vy
    @4
    @11
    cvv
    cardiun
    ax-mp
    adantl
    @31
    @5
    @32
    ccrd
    @29
    @5
    @32
    wceq
    #
    @30
    @35
    @29
    @37
    @36
    vy
    @4
    cvv
    alephlim
    mpan
    adantr
    #
    fveq2d
    @38
    3eqtr4d
    ex
    tfinds
    @0
    wn
    #
    c0
    ccrd
    cfv
    c0
    @2
    @1
    card0
    @39
    @1
    c0
    ccrd
    @0
    cA
    cale
    cdm
    #
    wcel
    @1
    c0
    wceq
    @40
    con0
    cA
    cale
    con0
    wfn
    @40
    con0
    wceq
    alephfnon
    con0
    cale
    fndm
    ax-mp
    eleq2i
    cA
    cale
    ndmfv
    sylnbir
    #
    fveq2d
    @41
    3eqtr4a
    pm2.61i
end
