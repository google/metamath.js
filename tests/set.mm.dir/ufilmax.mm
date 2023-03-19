include "cufil.mm"
include "cfv.mm"
include "wcel.mm"
include "cfil.mm"
include "wss.mm"
include "w3a.mm"
include "simp3.mm"
include "cv.mm"
include "wi.mm"
include "filelss.mm"
include "ex.mm"
include "3ad2ant2.mm"
include "wa.mm"
include "wn.mm"
include "cdif.mm"
include "wb.mm"
include "ufilb.mm"
include "3ad2antl1.mm"
include "simpl3.mm"
include "sseld.mm"
include "cfbas.mm"
include "filfbas.mm"
include "fbncp.mm"
include "syl.mm"
include "con2d.mm"
include "adantr.mm"
include "syld.mm"
include "sylbid.mm"
include "con4d.mm"
include "com23.mm"
include "mpdd.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem ufilmax
  let cF: class F
  let cG: class G
  let cX: class X
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let cS: class S


  assert |- ( ( F e. ( UFil ` X ) /\ G e. ( Fil ` X ) /\ F C_ G ) -> F = G )

  proof
    cF
    cX
    cufil
    cfv
    wcel
    #
    cG
    cX
    cfil
    cfv
    wcel
    #
    cF
    cG
    wss
    #
    w3a
    #
    cF
    cG
    @0
    @1
    @2
    simp3
    @3
    vx
    cG
    cF
    @3
    vx
    cv
    #
    cG
    wcel
    #
    @4
    cX
    wss
    #
    @4
    cF
    wcel
    #
    @1
    @0
    @5
    @6
    wi
    @2
    @1
    @5
    @6
    @4
    cG
    cX
    filelss
    ex
    3ad2ant2
    @3
    @6
    @5
    @7
    @3
    @6
    @5
    @7
    wi
    @3
    @6
    wa
    #
    @7
    @5
    @8
    @7
    wn
    #
    cX
    @4
    cdif
    #
    cF
    wcel
    #
    @5
    wn
    #
    @0
    @1
    @6
    @9
    @11
    wb
    @2
    @4
    cF
    cX
    ufilb
    3ad2antl1
    @8
    @11
    @10
    cG
    wcel
    #
    @12
    @8
    cF
    cG
    @10
    @0
    @1
    @2
    @6
    simpl3
    sseld
    @3
    @13
    @12
    wi
    #
    @6
    @1
    @0
    @14
    @2
    @1
    @5
    @13
    @1
    cG
    cX
    cfbas
    cfv
    wcel
    #
    @5
    @13
    wn
    #
    wi
    cG
    cX
    filfbas
    @15
    @5
    @16
    @4
    cX
    cG
    cX
    fbncp
    ex
    syl
    con2d
    3ad2ant2
    adantr
    syld
    sylbid
    con4d
    ex
    com23
    mpdd
    ssrdv
    eqssd
end
