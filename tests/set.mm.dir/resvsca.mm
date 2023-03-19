include "cvv.mm"
include "wcel.mm"
include "cress.mm"
include "co.mm"
include "csca.mm"
include "cfv.mm"
include "wceq.mm"
include "wss.mm"
include "wa.mm"
include "wi.mm"
include "w3a.mm"
include "fvex.mm"
include "eqeltri.mm"
include "eqid.mm"
include "ressid2.mm"
include "mp3an2.mm"
include "3adant2.mm"
include "resvid2.mm"
include "fveq2d.mm"
include "3eqtr4a.mm"
include "3expib.mm"
include "wn.mm"
include "cnx.mm"
include "cop.mm"
include "csts.mm"
include "simp2.mm"
include "ovex.mm"
include "scaid.mm"
include "setsid.mm"
include "sylancl.mm"
include "resvval2.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "c0.mm"
include "0fv.mm"
include "0ex.mm"
include "strfvn.mm"
include "ress0.mm"
include "3eqtr4ri.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "oveq1d.mm"
include "cresv.mm"
include "reldmresv.mm"
include "ovprc1.mm"
include "adantr.mm"
include "pm2.61ian.mm"

theorem resvsca
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cV: class V
  let cW: class W
  let vw: setvar w
  let vx: setvar x
  assume resvsca.r: |- R = ( W |`v A )
  assume resvsca.f: |- F = ( Scalar ` W )
  assume resvsca.b: |- B = ( Base ` F )


  assert |- ( A e. V -> ( F |`s A ) = ( Scalar ` R ) )

  proof
    cW
    cvv
    wcel
    #
    cA
    cV
    wcel
    #
    cF
    cA
    cress
    co
    #
    cR
    csca
    cfv
    #
    wceq
    #
    cB
    cA
    wss
    #
    @0
    @1
    wa
    @4
    wi
    @5
    @0
    @1
    @4
    @5
    @0
    @1
    w3a
    #
    cF
    cW
    csca
    cfv
    #
    @2
    @3
    resvsca.f
    @5
    @1
    @2
    cF
    wceq
    #
    @0
    @5
    cF
    cvv
    wcel
    @1
    @8
    cF
    @7
    cvv
    resvsca.f
    cW
    csca
    fvex
    eqeltri
    cA
    cB
    @2
    cF
    cvv
    cV
    @2
    eqid
    resvsca.b
    ressid2
    mp3an2
    3adant2
    @6
    cR
    cW
    csca
    cA
    cB
    cR
    cF
    cW
    cvv
    cV
    resvsca.r
    resvsca.f
    resvsca.b
    resvid2
    fveq2d
    3eqtr4a
    3expib
    @5
    wn
    #
    @0
    @1
    @4
    @9
    @0
    @1
    w3a
    #
    @2
    cW
    cnx
    csca
    cfv
    #
    @2
    cop
    csts
    co
    #
    csca
    cfv
    #
    @3
    @10
    @0
    @2
    cvv
    wcel
    @2
    @13
    wceq
    @9
    @0
    @1
    simp2
    cF
    cA
    cress
    ovex
    cvv
    @2
    csca
    cvv
    cW
    scaid
    setsid
    sylancl
    @10
    cR
    @12
    csca
    cA
    cB
    cR
    cF
    cW
    cvv
    cV
    resvsca.r
    resvsca.f
    resvsca.b
    resvval2
    fveq2d
    eqtr4d
    3expib
    pm2.61i
    @0
    wn
    #
    @4
    @1
    @14
    c0
    cA
    cress
    co
    #
    c0
    csca
    cfv
    #
    @2
    @3
    @11
    c0
    cfv
    c0
    @16
    @15
    @11
    0fv
    c0
    csca
    @11
    0ex
    scaid
    strfvn
    cA
    ress0
    3eqtr4ri
    @14
    cF
    c0
    cA
    cress
    @14
    cF
    @7
    c0
    resvsca.f
    cW
    csca
    fvprc
    syl5eq
    oveq1d
    @14
    cR
    c0
    csca
    @14
    cR
    cW
    cA
    cresv
    co
    c0
    resvsca.r
    cW
    cA
    cresv
    reldmresv
    ovprc1
    syl5eq
    fveq2d
    3eqtr4a
    adantr
    pm2.61ian
end
