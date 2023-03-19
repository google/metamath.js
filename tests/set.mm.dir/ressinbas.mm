include "wcel.mm"
include "cvv.mm"
include "cress.mm"
include "co.mm"
include "cin.mm"
include "wceq.mm"
include "elex.mm"
include "wss.mm"
include "wa.mm"
include "w3a.mm"
include "eqid.mm"
include "ressid2.mm"
include "ssid.mm"
include "incom.mm"
include "df-ss.mm"
include "biimpi.mm"
include "syl5eq.mm"
include "syl5sseqr.mm"
include "inex1g.mm"
include "syl3an.mm"
include "eqtr4d.mm"
include "3expb.mm"
include "wn.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "csts.mm"
include "inass.mm"
include "inidm.mm"
include "ineq2i.mm"
include "eqtr2i.mm"
include "opeq2i.mm"
include "oveq2i.mm"
include "ressval2.mm"
include "inss1.mm"
include "sstr.mm"
include "mpan2.mm"
include "con3i.mm"
include "3eqtr4a.mm"
include "pm2.61ian.mm"
include "c0.mm"
include "reldmress.mm"
include "ovprc1.mm"
include "adantr.mm"
include "syl.mm"

theorem ressinbas
  let cA: class A
  let cB: class B
  let cW: class W
  let cX: class X
  assume ressid.1: |- B = ( Base ` W )


  assert |- ( A e. X -> ( W |`s A ) = ( W |`s ( A i^i B ) ) )

  proof
    cA
    cX
    wcel
    cA
    cvv
    wcel
    #
    cW
    cA
    cress
    co
    #
    cW
    cA
    cB
    cin
    #
    cress
    co
    #
    wceq
    #
    cA
    cX
    elex
    cW
    cvv
    wcel
    #
    @0
    @4
    cB
    cA
    wss
    #
    @5
    @0
    wa
    @4
    @6
    @5
    @0
    @4
    @6
    @5
    @0
    w3a
    @1
    cW
    @3
    cA
    cB
    @1
    cW
    cvv
    cvv
    @1
    eqid
    #
    ressid.1
    ressid2
    @6
    cB
    @2
    wss
    #
    @5
    @5
    @0
    @2
    cvv
    wcel
    #
    @3
    cW
    wceq
    @6
    cB
    cB
    @2
    cB
    ssid
    @6
    @2
    cB
    cA
    cin
    #
    cB
    cA
    cB
    incom
    @6
    @10
    cB
    wceq
    cB
    cA
    df-ss
    biimpi
    syl5eq
    syl5sseqr
    cW
    cvv
    elex
    #
    cA
    cB
    cvv
    inex1g
    #
    @2
    cB
    @3
    cW
    cvv
    cvv
    @3
    eqid
    #
    ressid.1
    ressid2
    syl3an
    eqtr4d
    3expb
    @6
    wn
    #
    @5
    @0
    @4
    @14
    @5
    @0
    w3a
    cW
    cnx
    cbs
    cfv
    #
    @2
    cop
    #
    csts
    co
    cW
    @15
    @2
    cB
    cin
    #
    cop
    #
    csts
    co
    #
    @1
    @3
    @16
    @18
    cW
    csts
    @2
    @17
    @15
    @17
    cA
    cB
    cB
    cin
    #
    cin
    @2
    cA
    cB
    cB
    inass
    @20
    cB
    cA
    cB
    inidm
    ineq2i
    eqtr2i
    opeq2i
    oveq2i
    cA
    cB
    @1
    cW
    cvv
    cvv
    @7
    ressid.1
    ressval2
    @14
    @8
    wn
    @5
    @5
    @0
    @9
    @3
    @19
    wceq
    @8
    @6
    @8
    @2
    cA
    wss
    @6
    cA
    cB
    inss1
    cB
    @2
    cA
    sstr
    mpan2
    con3i
    @11
    @12
    @2
    cB
    @3
    cW
    cvv
    cvv
    @13
    ressid.1
    ressval2
    syl3an
    3eqtr4a
    3expb
    pm2.61ian
    @5
    wn
    #
    @4
    @0
    @21
    @1
    c0
    @3
    cW
    cA
    cress
    reldmress
    ovprc1
    cW
    @2
    cress
    reldmress
    ovprc1
    eqtr4d
    adantr
    pm2.61ian
    syl
end
