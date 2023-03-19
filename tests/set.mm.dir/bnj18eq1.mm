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
include "eleq2d.mm"
include "anbi1d.mm"
include "rexbidv2.mm"
include "df-iun.mm"
include "3eqtr4g.mm"
include "df-bnj18.mm"

theorem bnj18eq1
  let cA: class A
  let cR: class R
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y


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
    vx
    cv
    @15
    wcel
    #
    vf
    @14
    wrex
    #
    vx
    cab
    @23
    vf
    @21
    wrex
    #
    vx
    cab
    @16
    @22
    @0
    @24
    @25
    vx
    @0
    @23
    @23
    vf
    @14
    @21
    @0
    @1
    @14
    wcel
    @1
    @21
    wcel
    @23
    @0
    @14
    @21
    @1
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
    eleq2d
    anbi1d
    rexbidv2
    abbidv
    vf
    vx
    @14
    @15
    df-iun
    vf
    vx
    @21
    @15
    df-iun
    3eqtr4g
    vy
    cA
    cR
    vf
    vi
    vn
    cX
    df-bnj18
    vy
    cA
    cR
    vf
    vi
    vn
    cY
    df-bnj18
    3eqtr4g
end
