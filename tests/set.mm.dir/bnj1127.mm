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
include "wss.mm"
include "cep.mm"
include "wbr.mm"
include "wsbc.mm"
include "w3a.mm"
include "wrex.mm"
include "cab.mm"
include "biid.mm"
include "eqid.mm"
include "bnj1128.mm"

theorem bnj1127
  let cA: class A
  let cR: class R
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let vy: setvar y


  assert |- ( Y e. _trCl ( X , A , R ) -> Y e. A )

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
    @9
    @5
    cA
    wss
    wi
    #
    vj
    cv
    #
    @2
    cep
    wbr
    @10
    vi
    @11
    wsbc
    #
    wi
    vj
    @4
    wral
    #
    vy
    cA
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
    @7
    cR
    vf
    vi
    vj
    vn
    cX
    cY
    @1
    vi
    @11
    wsbc
    #
    @6
    vi
    @11
    wsbc
    #
    @9
    vi
    @11
    wsbc
    #
    @12
    @1
    biid
    @6
    biid
    @7
    eqid
    @14
    eqid
    @9
    biid
    @10
    biid
    @13
    biid
    @15
    biid
    @16
    biid
    @17
    biid
    @12
    biid
    bnj1128
end
