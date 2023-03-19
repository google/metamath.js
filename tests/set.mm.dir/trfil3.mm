include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "cdif.mm"
include "wn.mm"
include "trfil2.mm"
include "wrex.mm"
include "dfral2.mm"
include "wb.mm"
include "wceq.mm"
include "nne.mm"
include "filelss.mm"
include "reldisj.mm"
include "syl.mm"
include "syl5bb.mm"
include "rexbidva.mm"
include "adantr.mm"
include "difssd.mm"
include "elfilss.mm"
include "sylan2.mm"
include "bitr4d.mm"
include "notbid.mm"
include "bitrd.mm"

theorem trfil3
  let cA: class A
  let cL: class L
  let cY: class Y
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( L e. ( Fil ` Y ) /\ A C_ Y ) -> ( ( L |`t A ) e. ( Fil ` A ) <-> -. ( Y \ A ) e. L ) )

  proof
    cL
    cY
    cfil
    cfv
    wcel
    #
    cA
    cY
    wss
    #
    wa
    #
    cL
    cA
    crest
    co
    cA
    cfil
    cfv
    wcel
    vv
    cv
    #
    cA
    cin
    #
    c0
    wne
    #
    vv
    cL
    wral
    #
    cY
    cA
    cdif
    #
    cL
    wcel
    #
    wn
    #
    vv
    cA
    cL
    cY
    trfil2
    @6
    @5
    wn
    #
    vv
    cL
    wrex
    #
    wn
    @2
    @9
    @5
    vv
    cL
    dfral2
    @2
    @11
    @8
    @2
    @11
    @3
    @7
    wss
    #
    vv
    cL
    wrex
    #
    @8
    @0
    @11
    @13
    wb
    @1
    @0
    @10
    @12
    vv
    cL
    @10
    @4
    c0
    wceq
    #
    @0
    @3
    cL
    wcel
    wa
    #
    @12
    @4
    c0
    nne
    @15
    @3
    cY
    wss
    @14
    @12
    wb
    @3
    cL
    cY
    filelss
    @3
    cA
    cY
    reldisj
    syl
    syl5bb
    rexbidva
    adantr
    @1
    @0
    @7
    cY
    wss
    @8
    @13
    wb
    @1
    cY
    cA
    difssd
    vv
    @7
    cL
    cY
    elfilss
    sylan2
    bitr4d
    notbid
    syl5bb
    bitrd
end
