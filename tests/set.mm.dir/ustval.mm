include "wcel.mm"
include "cv.mm"
include "cxp.mm"
include "cpw.mm"
include "wss.mm"
include "wel.mm"
include "wi.mm"
include "wral.mm"
include "cin.mm"
include "cid.mm"
include "cres.mm"
include "ccnv.mm"
include "ccom.mm"
include "wrex.mm"
include "w3a.mm"
include "cab.mm"
include "cvv.mm"
include "cust.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-ust.mm"
include "a1i.mm"
include "id.mm"
include "sqxpeqd.mm"
include "pweqd.mm"
include "sseq2d.mm"
include "eleq1d.mm"
include "raleqdv.mm"
include "reseq2.mm"
include "sseq1d.mm"
include "3anbi1d.mm"
include "3anbi13d.mm"
include "ralbidv.mm"
include "3anbi123d.mm"
include "abbidv.mm"
include "adantl.mm"
include "elex.mm"
include "simp1.mm"
include "ss2abi.mm"
include "df-pw.mm"
include "sseqtr4i.mm"
include "sqxpexg.mm"
include "pwexg.mm"
include "3syl.mm"
include "ssexg.mm"
include "sylancr.mm"
include "fvmptd.mm"

theorem ustval
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cV: class V
  let cX: class X
  let vx: setvar x

  disjoint u v
  disjoint u w
  disjoint X u
  disjoint v w
  disjoint X v
  disjoint X w
  disjoint V x
  disjoint u x
  disjoint v x
  disjoint w x
  disjoint X x
  assert |- ( X e. V -> ( UnifOn ` X ) = { u | ( u C_ ~P ( X X. X ) /\ ( X X. X ) e. u /\ A. v e. u ( A. w e. ~P ( X X. X ) ( v C_ w -> w e. u ) /\ A. w e. u ( v i^i w ) e. u /\ ( ( _I |` X ) C_ v /\ `' v e. u /\ E. w e. u ( w o. w ) C_ v ) ) ) } )

  proof
    cX
    cV
    wcel
    #
    vx
    cX
    vu
    cv
    #
    vx
    cv
    #
    @2
    cxp
    #
    cpw
    #
    wss
    #
    @3
    @1
    wcel
    #
    vv
    cv
    #
    vw
    cv
    #
    wss
    vw
    vu
    wel
    wi
    #
    vw
    @4
    wral
    #
    @7
    @8
    cin
    @1
    wcel
    vw
    @1
    wral
    #
    cid
    @2
    cres
    #
    @7
    wss
    #
    @7
    ccnv
    @1
    wcel
    #
    @8
    @8
    ccom
    @7
    wss
    vw
    @1
    wrex
    #
    w3a
    #
    w3a
    #
    vv
    @1
    wral
    #
    w3a
    #
    vu
    cab
    #
    @1
    cX
    cX
    cxp
    #
    cpw
    #
    wss
    #
    @21
    @1
    wcel
    #
    @9
    vw
    @22
    wral
    #
    @11
    cid
    cX
    cres
    #
    @7
    wss
    #
    @14
    @15
    w3a
    #
    w3a
    #
    vv
    @1
    wral
    #
    w3a
    #
    vu
    cab
    #
    cvv
    cust
    cvv
    cust
    vx
    cvv
    @20
    cmpt
    wceq
    @0
    vx
    vw
    vv
    vu
    df-ust
    a1i
    @2
    cX
    wceq
    #
    @20
    @32
    wceq
    @0
    @33
    @19
    @31
    vu
    @33
    @5
    @23
    @6
    @24
    @18
    @30
    @33
    @4
    @22
    @1
    @33
    @3
    @21
    @33
    @2
    cX
    @33
    id
    sqxpeqd
    #
    pweqd
    #
    sseq2d
    @33
    @3
    @21
    @1
    @34
    eleq1d
    @33
    @17
    @29
    vv
    @1
    @33
    @10
    @25
    @16
    @28
    @11
    @33
    @9
    vw
    @4
    @22
    @35
    raleqdv
    @33
    @13
    @27
    @14
    @15
    @33
    @12
    @26
    @7
    @2
    cX
    cid
    reseq2
    sseq1d
    3anbi1d
    3anbi13d
    ralbidv
    3anbi123d
    abbidv
    adantl
    cX
    cV
    elex
    @0
    @32
    @22
    cpw
    #
    wss
    @36
    cvv
    wcel
    #
    @32
    cvv
    wcel
    @32
    @23
    vu
    cab
    @36
    @31
    @23
    vu
    @23
    @24
    @30
    simp1
    ss2abi
    vu
    @22
    df-pw
    sseqtr4i
    @0
    @21
    cvv
    wcel
    @22
    cvv
    wcel
    @37
    cX
    cV
    sqxpexg
    @21
    cvv
    pwexg
    @22
    cvv
    pwexg
    3syl
    @32
    @36
    cvv
    ssexg
    sylancr
    fvmptd
end
