include "cfunpart.mm"
include "cfv.mm"
include "cimage.mm"
include "csingle.mm"
include "ccom.mm"
include "cvv.mm"
include "csingles.mm"
include "cxp.mm"
include "cin.mm"
include "cdm.mm"
include "cres.mm"
include "df-funpart.mm"
include "fveq1i.mm"
include "wcel.mm"
include "wceq.mm"
include "fvres.mm"
include "wn.mm"
include "c0.mm"
include "nfvres.mm"
include "wi.mm"
include "cv.mm"
include "wbr.mm"
include "weu.mm"
include "csn.mm"
include "cima.mm"
include "wex.mm"
include "funpartlem.mm"
include "eusn.mm"
include "bitr4i.mm"
include "cop.mm"
include "wb.mm"
include "vex.mm"
include "elimasng.mm"
include "mpan2.mm"
include "df-br.mm"
include "syl6bbr.mm"
include "eubidv.mm"
include "syl5bb.mm"
include "notbid.mm"
include "tz6.12-2.mm"
include "syl6bi.mm"
include "fvprc.mm"
include "a1d.mm"
include "pm2.61i.mm"
include "eqtr4d.mm"
include "eqtri.mm"

theorem funpartfv
  let cA: class A
  let cF: class F
  let vx: setvar x


  assert |- ( Funpart F ` A ) = ( F ` A )

  proof
    cA
    cF
    cfunpart
    #
    cfv
    cA
    cF
    cF
    cimage
    csingle
    ccom
    cvv
    csingles
    cxp
    cin
    cdm
    #
    cres
    #
    cfv
    #
    cA
    cF
    cfv
    #
    cA
    @0
    @2
    cF
    df-funpart
    fveq1i
    cA
    @1
    wcel
    #
    @3
    @4
    wceq
    cA
    @1
    cF
    fvres
    @5
    wn
    #
    @3
    c0
    @4
    cA
    @1
    cF
    nfvres
    cA
    cvv
    wcel
    #
    @6
    @4
    c0
    wceq
    #
    wi
    @7
    @6
    cA
    vx
    cv
    #
    cF
    wbr
    #
    vx
    weu
    #
    wn
    @8
    @7
    @5
    @11
    @5
    @9
    cF
    cA
    csn
    cima
    #
    wcel
    #
    vx
    weu
    #
    @7
    @11
    @5
    @12
    @9
    csn
    wceq
    vx
    wex
    @14
    vx
    cA
    cF
    funpartlem
    vx
    @12
    eusn
    bitr4i
    @7
    @13
    @10
    vx
    @7
    @13
    cA
    @9
    cop
    cF
    wcel
    #
    @10
    @7
    @9
    cvv
    wcel
    @13
    @15
    wb
    vx
    vex
    cF
    cA
    @9
    cvv
    cvv
    elimasng
    mpan2
    cA
    @9
    cF
    df-br
    syl6bbr
    eubidv
    syl5bb
    notbid
    vx
    cA
    cF
    tz6.12-2
    syl6bi
    @7
    wn
    @8
    @6
    cA
    cF
    fvprc
    a1d
    pm2.61i
    eqtr4d
    pm2.61i
    eqtri
end
