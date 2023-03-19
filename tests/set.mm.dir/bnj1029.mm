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
include "w-bnj15.mm"
include "c-bnj18.mm"
include "w3a.mm"
include "wel.mm"
include "wa.mm"
include "wrex.mm"
include "cab.mm"
include "cop.mm"
include "cun.mm"
include "wsbc.mm"
include "biid.mm"
include "eqid.mm"
include "bnj907.mm"

theorem bnj1029
  let cA: class A
  let cR: class R
  let cX: class X
  let vf: setvar f
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( R _FrSe A /\ X e. A ) -> _TrFo ( _trCl ( X , A , R ) , A , R ) )

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
    #
    c-bnj14
    #
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
    @8
    w-bnj17
    #
    cA
    cR
    w-bnj15
    cX
    cA
    wcel
    @6
    cA
    cR
    cX
    c-bnj18
    wcel
    vz
    cv
    @7
    wcel
    w-bnj17
    #
    vm
    cv
    #
    com
    wcel
    @4
    @13
    csuc
    wceq
    vp
    cv
    #
    @4
    csuc
    wceq
    w3a
    #
    vi
    vn
    wel
    @6
    @5
    wcel
    wa
    #
    vy
    vz
    cA
    @10
    @1
    @8
    w3a
    vn
    @9
    wrex
    vf
    cab
    #
    vy
    @13
    @0
    cfv
    @7
    ciun
    #
    @9
    cR
    vf
    vi
    vm
    vn
    @0
    @4
    @18
    cop
    csn
    cun
    #
    cX
    vp
    @1
    vn
    @14
    wsbc
    #
    @8
    vn
    @14
    wsbc
    #
    @11
    vn
    @14
    wsbc
    #
    @20
    vf
    @19
    wsbc
    #
    @21
    vf
    @19
    wsbc
    #
    @22
    vf
    @19
    wsbc
    #
    @1
    biid
    @8
    biid
    @11
    biid
    @12
    biid
    @15
    biid
    @16
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
    @9
    eqid
    @17
    eqid
    @18
    eqid
    @19
    eqid
    bnj907
end
