include "wcel.mm"
include "carchi.mm"
include "cinftm.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "df-archi.mm"
include "elab2g.mm"
include "cxp.mm"
include "wss.mm"
include "wb.mm"
include "inftmrel.mm"
include "cop.mm"
include "wi.mm"
include "ss0b.mm"
include "ssrel2.mm"
include "syl5bbr.mm"
include "noel.mm"
include "nbn.mm"
include "breqi.mm"
include "df-br.mm"
include "bitri.mm"
include "xchnxbir.mm"
include "pm2.21i.mm"
include "dfbi2.mm"
include "mpbiran2.mm"
include "2ralbii.mm"
include "syl6bbr.mm"
include "syl.mm"
include "bitrd.mm"

theorem isarchi
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.lt: class .<
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vw: setvar w
  assume isarchi.b: |- B = ( Base ` W )
  assume isarchi.0: |- .0. = ( 0g ` W )
  assume isarchi.i: |- .< = ( <<< ` W )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint W x
  disjoint W y
  disjoint w x
  disjoint w y
  disjoint W w
  assert |- ( W e. V -> ( W e. Archi <-> A. x e. B A. y e. B -. x .< y ) )

  proof
    cW
    cV
    wcel
    #
    cW
    carchi
    wcel
    cW
    cinftm
    cfv
    #
    c0
    wceq
    #
    vx
    cv
    #
    vy
    cv
    #
    c.lt
    wbr
    #
    wn
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    vw
    cv
    #
    cinftm
    cfv
    #
    c0
    wceq
    @2
    vw
    cW
    carchi
    cV
    @8
    cW
    wceq
    @9
    @1
    c0
    @8
    cW
    cinftm
    fveq2
    eqeq1d
    vw
    df-archi
    elab2g
    @0
    @1
    cB
    cB
    cxp
    wss
    #
    @2
    @7
    wb
    cB
    cV
    cW
    isarchi.b
    inftmrel
    @10
    @2
    @3
    @4
    cop
    #
    @1
    wcel
    #
    @11
    c0
    wcel
    #
    wi
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @7
    @2
    @1
    c0
    wss
    @10
    @15
    @1
    ss0b
    vx
    vy
    cB
    cB
    @1
    c0
    ssrel2
    syl5bbr
    @6
    @14
    vx
    vy
    cB
    cB
    @6
    @12
    @13
    wb
    #
    @14
    @12
    @16
    @5
    @13
    @12
    @11
    noel
    #
    nbn
    @5
    @3
    @4
    @1
    wbr
    @12
    @3
    @4
    c.lt
    @1
    isarchi.i
    breqi
    @3
    @4
    @1
    df-br
    bitri
    xchnxbir
    @16
    @14
    @13
    @12
    wi
    @13
    @12
    @17
    pm2.21i
    @12
    @13
    dfbi2
    mpbiran2
    bitri
    2ralbii
    syl6bbr
    syl
    bitrd
end
