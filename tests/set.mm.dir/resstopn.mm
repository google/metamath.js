include "cvv.mm"
include "wcel.mm"
include "crest.mm"
include "co.mm"
include "ctopn.mm"
include "cfv.mm"
include "wceq.mm"
include "cts.mm"
include "cbs.mm"
include "cin.mm"
include "fvex.mm"
include "restco.mm"
include "mp3an12.mm"
include "eqid.mm"
include "resstset.mm"
include "incom.mm"
include "ressbas.mm"
include "syl5eq.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "topnval.mm"
include "eqtr4i.mm"
include "oveq1i.mm"
include "3eqtr3g.mm"
include "wn.mm"
include "c0.mm"
include "wa.mm"
include "simpr.mm"
include "con3i.mm"
include "cxp.mm"
include "wfn.mm"
include "cdm.mm"
include "restfn.mm"
include "fndm.mm"
include "ax-mp.mm"
include "ndmov.mm"
include "syl.mm"
include "cress.mm"
include "reldmress.mm"
include "ovprc2.mm"
include "fveq2d.mm"
include "c9.mm"
include "df-tset.mm"
include "str0.mm"
include "syl6eqr.mm"
include "oveq1d.mm"
include "0rest.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem resstopn
  let cA: class A
  let cH: class H
  let cJ: class J
  let cK: class K
  assume resstopn.1: |- H = ( K |`s A )
  assume resstopn.2: |- J = ( TopOpen ` K )


  assert |- ( J |`t A ) = ( TopOpen ` H )

  proof
    cA
    cvv
    wcel
    #
    cJ
    cA
    crest
    co
    #
    cH
    ctopn
    cfv
    #
    wceq
    @0
    cK
    cts
    cfv
    #
    cK
    cbs
    cfv
    #
    crest
    co
    #
    cA
    crest
    co
    #
    cH
    cts
    cfv
    #
    cH
    cbs
    cfv
    #
    crest
    co
    #
    @1
    @2
    @0
    @6
    @3
    @4
    cA
    cin
    #
    crest
    co
    #
    @9
    @3
    cvv
    wcel
    @4
    cvv
    wcel
    @0
    @6
    @11
    wceq
    cK
    cts
    fvex
    cK
    cbs
    fvex
    @4
    cA
    @3
    cvv
    cvv
    cvv
    restco
    mp3an12
    @0
    @3
    @7
    @10
    @8
    crest
    cA
    cK
    cH
    @3
    cvv
    resstopn.1
    @3
    eqid
    #
    resstset
    @0
    @10
    cA
    @4
    cin
    @8
    @4
    cA
    incom
    cA
    @4
    cH
    cvv
    cK
    resstopn.1
    @4
    eqid
    #
    ressbas
    syl5eq
    oveq12d
    eqtrd
    @5
    cJ
    cA
    crest
    @5
    cK
    ctopn
    cfv
    cJ
    @4
    @3
    cK
    @13
    @12
    topnval
    resstopn.2
    eqtr4i
    oveq1i
    @8
    @7
    cH
    @8
    eqid
    @7
    eqid
    topnval
    #
    3eqtr3g
    @0
    wn
    #
    @1
    c0
    @2
    @15
    cJ
    cvv
    wcel
    #
    @0
    wa
    #
    wn
    @1
    c0
    wceq
    @17
    @0
    @16
    @0
    simpr
    con3i
    cJ
    cA
    cvv
    crest
    crest
    cvv
    cvv
    cxp
    #
    wfn
    crest
    cdm
    @18
    wceq
    restfn
    @18
    crest
    fndm
    ax-mp
    ndmov
    syl
    @15
    @9
    c0
    @8
    crest
    co
    @2
    c0
    @15
    @7
    c0
    @8
    crest
    @15
    @7
    c0
    cts
    cfv
    c0
    @15
    cH
    c0
    cts
    @15
    cH
    cK
    cA
    cress
    co
    c0
    resstopn.1
    cK
    cA
    cress
    reldmress
    ovprc2
    syl5eq
    fveq2d
    cts
    c9
    df-tset
    str0
    syl6eqr
    oveq1d
    @14
    @8
    0rest
    3eqtr3g
    eqtr4d
    pm2.61i
end
