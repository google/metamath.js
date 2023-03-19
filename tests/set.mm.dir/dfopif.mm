include "cop.mm"
include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "cpr.mm"
include "w3a.mm"
include "cab.mm"
include "wa.mm"
include "c0.mm"
include "cif.mm"
include "df-op.mm"
include "df-3an.mm"
include "abbii.mm"
include "wceq.mm"
include "iftrue.mm"
include "ibar.mm"
include "abbi2dv.mm"
include "eqtr2d.mm"
include "wn.mm"
include "wss.mm"
include "pm2.21.mm"
include "adantrd.mm"
include "abssdv.mm"
include "ss0.mm"
include "syl.mm"
include "iffalse.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "3eqtri.mm"

theorem dfopif
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- <. A , B >. = if ( ( A e. _V /\ B e. _V ) , { { A } , { A , B } } , (/) )

  proof
    cA
    cB
    cop
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    vx
    cv
    #
    cA
    csn
    cA
    cB
    cpr
    cpr
    #
    wcel
    #
    w3a
    #
    vx
    cab
    @0
    @1
    wa
    #
    @4
    wa
    #
    vx
    cab
    #
    @6
    @3
    c0
    cif
    #
    vx
    cA
    cB
    df-op
    @5
    @7
    vx
    @0
    @1
    @4
    df-3an
    abbii
    @6
    @8
    @9
    wceq
    @6
    @9
    @3
    @8
    @6
    @3
    c0
    iftrue
    @6
    @7
    vx
    @3
    @6
    @4
    ibar
    abbi2dv
    eqtr2d
    @6
    wn
    #
    @8
    c0
    @9
    @10
    @8
    c0
    wss
    @8
    c0
    wceq
    @10
    @7
    vx
    c0
    @10
    @6
    @2
    c0
    wcel
    #
    @4
    @6
    @11
    pm2.21
    adantrd
    abssdv
    @8
    ss0
    syl
    @6
    @3
    c0
    iffalse
    eqtr4d
    pm2.61i
    3eqtri
end
