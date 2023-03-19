include "wceq.mm"
include "cv.mm"
include "wfn.mm"
include "c0.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "csuc.mm"
include "wcel.mm"
include "ciun.mm"
include "wi.mm"
include "com.mm"
include "wral.mm"
include "w3a.mm"
include "csn.mm"
include "cdif.mm"
include "wrex.mm"
include "cab.mm"
include "cdm.mm"
include "c-bnj18.mm"
include "bnj602.mm"
include "eqeq2d.mm"
include "3anbi2d.mm"
include "rexbidv.mm"
include "abbidv.mm"
include "hbab1.mm"
include "bnj1316.mm"
include "syl.mm"
include "biid.mm"
include "eqid.mm"
include "bnj882.mm"
include "3eqtr4g.mm"

theorem bnj1318
  let cA: class A
  let cR: class R
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let vy: setvar y
  let vz: setvar z


  assert |- ( X = Y -> _trCl ( X , A , R ) = _trCl ( Y , A , R ) )

  proof
    cX
    cY
    wceq
    #
    vf
    vf
    cv
    #
    vn
    cv
    #
    wfn
    #
    c0
    @1
    cfv
    #
    cA
    cR
    cX
    c-bnj14
    #
    wceq
    #
    vi
    cv
    #
    csuc
    #
    @2
    wcel
    @8
    @1
    cfv
    vy
    @7
    @1
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
    w3a
    #
    vn
    com
    c0
    csn
    cdif
    #
    wrex
    #
    vf
    cab
    #
    vi
    @1
    cdm
    @9
    ciun
    #
    ciun
    #
    vf
    @3
    @4
    cA
    cR
    cY
    c-bnj14
    #
    wceq
    #
    @10
    w3a
    #
    vn
    @12
    wrex
    #
    vf
    cab
    #
    @15
    ciun
    #
    cA
    cR
    cX
    c-bnj18
    cA
    cR
    cY
    c-bnj18
    @0
    @14
    @21
    wceq
    @16
    @22
    wceq
    @0
    @13
    @20
    vf
    @0
    @11
    @19
    vn
    @12
    @0
    @6
    @18
    @3
    @10
    @0
    @5
    @17
    @4
    cA
    cR
    cX
    cY
    bnj602
    eqeq2d
    3anbi2d
    rexbidv
    abbidv
    vf
    vz
    @14
    @21
    @15
    @13
    vf
    vz
    hbab1
    @20
    vf
    vz
    hbab1
    bnj1316
    syl
    @6
    @10
    vy
    cA
    @14
    @12
    cR
    vf
    vi
    vn
    cX
    @6
    biid
    @10
    biid
    #
    @12
    eqid
    #
    @14
    eqid
    bnj882
    @18
    @10
    vy
    cA
    @21
    @12
    cR
    vf
    vi
    vn
    cY
    @18
    biid
    @23
    @24
    @21
    eqid
    bnj882
    3eqtr4g
end
