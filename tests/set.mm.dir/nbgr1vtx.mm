include "cvtx.mm"
include "cfv.mm"
include "wcel.mm"
include "chash.mm"
include "c1.mm"
include "wceq.mm"
include "cnbgr.mm"
include "co.mm"
include "c0.mm"
include "wi.mm"
include "wa.mm"
include "cv.mm"
include "cpr.mm"
include "wss.mm"
include "cedg.mm"
include "wrex.mm"
include "wn.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "wex.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "hash1snb.mm"
include "ax-mp.mm"
include "ral0.mm"
include "eleq2.mm"
include "simpr.mm"
include "sneq.mm"
include "adantr.mm"
include "difeq12d.mm"
include "difid.mm"
include "syl6eq.mm"
include "ex.mm"
include "elsni.mm"
include "syl11.mm"
include "sylbid.mm"
include "imp.mm"
include "raleqdv.mm"
include "mpbiri.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "impcom.mm"
include "nbgr0vtxlem.mm"
include "wnel.mm"
include "df-nel.mm"
include "eqid.mm"
include "nbgrnvtx0.mm"
include "sylbir.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem nbgr1vtx
  let cG: class G
  let cK: class K
  let ve: setvar e
  let vn: setvar n
  let vv: setvar v


  assert |- ( ( # ` ( Vtx ` G ) ) = 1 -> ( G NeighbVtx K ) = (/) )

  proof
    cK
    cG
    cvtx
    cfv
    #
    wcel
    #
    @0
    chash
    cfv
    c1
    wceq
    #
    cG
    cK
    cnbgr
    co
    c0
    wceq
    #
    wi
    @1
    @2
    @3
    @1
    @2
    wa
    ve
    vn
    cG
    cK
    @2
    @1
    cK
    vn
    cv
    cpr
    ve
    cv
    wss
    ve
    cG
    cedg
    cfv
    wrex
    wn
    #
    vn
    @0
    cK
    csn
    #
    cdif
    #
    wral
    #
    @2
    @0
    vv
    cv
    #
    csn
    #
    wceq
    #
    vv
    wex
    #
    @1
    @7
    wi
    #
    @0
    cvv
    wcel
    @2
    @11
    wb
    cG
    cvtx
    fvex
    @0
    cvv
    vv
    hash1snb
    ax-mp
    @10
    @12
    vv
    @10
    @1
    @7
    @10
    @1
    wa
    #
    @7
    @4
    vn
    c0
    wral
    @4
    vn
    ral0
    @13
    @4
    vn
    @6
    c0
    @10
    @1
    @6
    c0
    wceq
    #
    @10
    @1
    cK
    @9
    wcel
    #
    @14
    @0
    @9
    cK
    eleq2
    cK
    @8
    wceq
    #
    @10
    @14
    @15
    @16
    @10
    @14
    @16
    @10
    wa
    #
    @6
    @9
    @9
    cdif
    c0
    @17
    @0
    @9
    @5
    @9
    @16
    @10
    simpr
    @16
    @5
    @9
    wceq
    @10
    cK
    @8
    sneq
    adantr
    difeq12d
    @9
    difid
    syl6eq
    ex
    cK
    @8
    elsni
    syl11
    sylbid
    imp
    raleqdv
    mpbiri
    ex
    exlimiv
    sylbi
    impcom
    nbgr0vtxlem
    ex
    @1
    wn
    #
    @3
    @2
    @18
    cK
    @0
    wnel
    @3
    cK
    @0
    df-nel
    cG
    @0
    cK
    @0
    eqid
    nbgrnvtx0
    sylbir
    a1d
    pm2.61i
end
