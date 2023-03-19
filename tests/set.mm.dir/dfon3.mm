include "con0.mm"
include "cv.mm"
include "wpss.mm"
include "wtr.mm"
include "wa.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "cab.mm"
include "cvv.mm"
include "csset.mm"
include "ctrans.mm"
include "cxp.mm"
include "cin.mm"
include "cid.mm"
include "cep.mm"
include "cun.mm"
include "cdif.mm"
include "crn.mm"
include "dfon2.mm"
include "wceq.mm"
include "wb.mm"
include "abeq1.mm"
include "wn.mm"
include "wbr.mm"
include "wex.mm"
include "vex.mm"
include "elrn.mm"
include "wss.mm"
include "brin.mm"
include "brsset.mm"
include "brxp.mm"
include "mpbiran2.mm"
include "eltrans.mm"
include "bitri.mm"
include "anbi12i.mm"
include "wo.mm"
include "ioran.mm"
include "brun.mm"
include "ideq.mm"
include "epel.mm"
include "orbi12i.mm"
include "xchnxbir.mm"
include "brdif.mm"
include "dfpss2.mm"
include "anbi1i.mm"
include "an32.mm"
include "anass.mm"
include "3bitr4i.mm"
include "exbii.mm"
include "exanali.mm"
include "con2bii.mm"
include "eldif.mm"
include "mpbiran.mm"
include "bitr4i.mm"
include "mpgbir.mm"
include "eqtri.mm"

theorem dfon3
  let vx: setvar x
  let vy: setvar y


  assert |- On = ( _V \ ran ( ( SSet i^i ( Trans X. _V ) ) \ ( _I u. _E ) ) )

  proof
    con0
    vy
    cv
    #
    vx
    cv
    #
    wpss
    #
    @0
    wtr
    #
    wa
    #
    @0
    @1
    wcel
    #
    wi
    vy
    wal
    #
    vx
    cab
    #
    cvv
    csset
    ctrans
    cvv
    cxp
    #
    cin
    #
    cid
    cep
    cun
    #
    cdif
    #
    crn
    #
    cdif
    #
    vx
    vy
    dfon2
    @7
    @13
    wceq
    @6
    @1
    @13
    wcel
    #
    wb
    vx
    @6
    vx
    @13
    abeq1
    @6
    @1
    @12
    wcel
    #
    wn
    #
    @14
    @15
    @6
    @15
    @0
    @1
    @11
    wbr
    #
    vy
    wex
    #
    @6
    wn
    #
    vy
    @1
    @11
    vx
    vex
    #
    elrn
    @18
    @4
    @5
    wn
    #
    wa
    #
    vy
    wex
    @19
    @17
    @22
    vy
    @0
    @1
    @9
    wbr
    #
    @0
    @1
    @10
    wbr
    #
    wn
    #
    wa
    @0
    @1
    wss
    #
    @3
    wa
    #
    @0
    @1
    wceq
    #
    wn
    #
    @21
    wa
    #
    wa
    #
    @17
    @22
    @23
    @27
    @25
    @30
    @23
    @0
    @1
    csset
    wbr
    #
    @0
    @1
    @8
    wbr
    #
    wa
    @27
    @0
    @1
    csset
    @8
    brin
    @32
    @26
    @33
    @3
    @0
    @1
    @20
    brsset
    @33
    @0
    ctrans
    wcel
    #
    @3
    @33
    @34
    @1
    cvv
    wcel
    #
    @20
    @0
    @1
    ctrans
    cvv
    brxp
    mpbiran2
    @0
    vy
    vex
    eltrans
    bitri
    anbi12i
    bitri
    @28
    @5
    wo
    #
    @30
    @24
    @28
    @5
    ioran
    @24
    @0
    @1
    cid
    wbr
    #
    @0
    @1
    cep
    wbr
    #
    wo
    @36
    @0
    @1
    cid
    cep
    brun
    @37
    @28
    @38
    @5
    @0
    @1
    @20
    ideq
    vy
    vx
    epel
    orbi12i
    bitri
    xchnxbir
    anbi12i
    @0
    @1
    @9
    @10
    brdif
    @22
    @27
    @29
    wa
    #
    @21
    wa
    @31
    @4
    @39
    @21
    @4
    @26
    @29
    wa
    #
    @3
    wa
    @39
    @2
    @40
    @3
    @0
    @1
    dfpss2
    anbi1i
    @26
    @29
    @3
    an32
    bitri
    anbi1i
    @27
    @29
    @21
    anass
    bitri
    3bitr4i
    exbii
    @4
    @5
    vy
    exanali
    bitri
    bitri
    con2bii
    @14
    @35
    @16
    @20
    @1
    cvv
    @12
    eldif
    mpbiran
    bitr4i
    mpgbir
    eqtri
end
