include "con0.mm"
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
include "cima.mm"
include "dfon3.mm"
include "cres.mm"
include "df-ima.mm"
include "df-res.mm"
include "indif1.mm"
include "eqtri.mm"
include "rneqi.mm"
include "difeq2i.mm"
include "eqtr4i.mm"

theorem dfon4



  assert |- On = ( _V \ ( ( SSet \ ( _I u. _E ) ) " Trans ) )

  proof
    con0
    cvv
    csset
    ctrans
    cvv
    cxp
    #
    cin
    cid
    cep
    cun
    #
    cdif
    #
    crn
    #
    cdif
    cvv
    csset
    @1
    cdif
    #
    ctrans
    cima
    #
    cdif
    dfon3
    @5
    @3
    cvv
    @5
    @4
    ctrans
    cres
    #
    crn
    @3
    @4
    ctrans
    df-ima
    @6
    @2
    @6
    @4
    @0
    cin
    @2
    @4
    ctrans
    df-res
    csset
    @0
    @1
    indif1
    eqtri
    rneqi
    eqtri
    difeq2i
    eqtr4i
end
