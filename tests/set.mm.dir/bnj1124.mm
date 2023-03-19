include "c0.mm"
include "cv.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "wceq.mm"
include "csuc.mm"
include "wcel.mm"
include "ciun.mm"
include "wi.mm"
include "com.mm"
include "wral.mm"
include "csn.mm"
include "cdif.mm"
include "wfn.mm"
include "w-bnj17.mm"
include "w3a.mm"
include "wrex.mm"
include "cab.mm"
include "cdm.mm"
include "wa.mm"
include "wss.mm"
include "wel.mm"
include "cep.mm"
include "wbr.mm"
include "wsbc.mm"
include "biid.mm"
include "eqid.mm"
include "bnj1030.mm"

theorem bnj1124
  let wth: wff th
  let wta: wff ta
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let vy: setvar y
  let vz: setvar z
  assume bnj1124.4: |- ( th <-> ( R _FrSe A /\ X e. A ) )
  assume bnj1124.5: |- ( ta <-> ( B e. _V /\ _TrFo ( B , A , R ) /\ _pred ( X , A , R ) C_ B ) )


  assert |- ( ( th /\ ta ) -> _trCl ( X , A , R ) C_ B )

  proof
    c0
    vf
    cv
    #
    cfv
    cA
    cR
    cX
    c-bnj14
    wceq
    #
    vi
    cv
    #
    csuc
    #
    vn
    cv
    #
    wcel
    @3
    @0
    cfv
    vy
    @2
    @0
    cfv
    #
    cA
    cR
    vy
    cv
    c-bnj14
    ciun
    wceq
    wi
    vi
    com
    wral
    #
    @4
    com
    c0
    csn
    cdif
    #
    wcel
    @0
    @4
    wfn
    #
    @1
    @6
    w-bnj17
    #
    wth
    wta
    @0
    @8
    @1
    @6
    w3a
    vn
    @7
    wrex
    vf
    cab
    #
    wcel
    #
    @2
    @0
    cdm
    wcel
    #
    wa
    @5
    cB
    wss
    wi
    #
    vi
    vn
    wel
    #
    vz
    cv
    @5
    wcel
    wa
    #
    vj
    vn
    wel
    vj
    cv
    #
    @2
    cep
    wbr
    #
    wa
    @13
    vi
    @16
    wsbc
    #
    wi
    #
    @17
    @18
    wi
    vj
    @4
    wral
    #
    vy
    vz
    cA
    cB
    @7
    cR
    vf
    vi
    vj
    vn
    @10
    cX
    @1
    vi
    @16
    wsbc
    #
    @6
    vi
    @16
    wsbc
    #
    @9
    vi
    @16
    wsbc
    #
    wth
    vi
    @16
    wsbc
    #
    wta
    vi
    @16
    wsbc
    #
    @18
    @15
    vi
    @16
    wsbc
    #
    @14
    @19
    @11
    @12
    w-bnj17
    #
    @1
    biid
    @6
    biid
    @9
    biid
    bnj1124.4
    bnj1124.5
    @15
    biid
    @7
    eqid
    @10
    eqid
    @13
    biid
    @20
    biid
    @21
    biid
    @22
    biid
    @23
    biid
    @24
    biid
    @25
    biid
    @26
    biid
    @18
    biid
    @19
    biid
    @27
    biid
    bnj1030
end
