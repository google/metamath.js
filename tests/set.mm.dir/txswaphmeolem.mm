include "cv.mm"
include "cop.mm"
include "cmpt2.mm"
include "ccom.mm"
include "cxp.mm"
include "cmpt.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "wtru.mm"
include "csn.mm"
include "ccnv.mm"
include "cuni.mm"
include "wcel.mm"
include "wa.mm"
include "opelxpi.mm"
include "ancoms.mm"
include "adantl.mm"
include "eqidd.mm"
include "sneq.mm"
include "cnveqd.mm"
include "unieqd.mm"
include "opswap.mm"
include "syl6eq.mm"
include "mpt2mpt.mm"
include "eqcomi.mm"
include "a1i.mm"
include "fmpt2co.mm"
include "trud.mm"
include "id.mm"
include "mptresid.mm"
include "3eqtr2i.mm"

theorem txswaphmeolem
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  let cY: class Y
  let cJ: class J
  let cK: class K
  let vz: setvar z

  disjoint x y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint K y
  disjoint x z
  disjoint y z
  disjoint X z
  disjoint Y z
  assert |- ( ( y e. Y , x e. X |-> <. x , y >. ) o. ( x e. X , y e. Y |-> <. y , x >. ) ) = ( _I |` ( X X. Y ) )

  proof
    vy
    vx
    cY
    cX
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    cmpt2
    #
    vx
    vy
    cX
    cY
    @1
    @0
    cop
    #
    cmpt2
    #
    ccom
    #
    vx
    vy
    cX
    cY
    @2
    cmpt2
    #
    vz
    cX
    cY
    cxp
    #
    vz
    cv
    #
    cmpt
    cid
    @8
    cres
    @6
    @7
    wceq
    wtru
    vx
    vy
    vz
    cX
    cY
    cY
    cX
    cxp
    #
    @4
    @9
    csn
    #
    ccnv
    #
    cuni
    #
    @2
    @5
    @3
    @0
    cX
    wcel
    #
    @1
    cY
    wcel
    #
    wa
    @4
    @10
    wcel
    #
    wtru
    @15
    @14
    @16
    @1
    @0
    cY
    cX
    opelxpi
    ancoms
    adantl
    wtru
    @5
    eqidd
    @3
    vz
    @10
    @13
    cmpt
    #
    wceq
    wtru
    @17
    @3
    vy
    vx
    vz
    cY
    cX
    @13
    @2
    @9
    @4
    wceq
    #
    @13
    @4
    csn
    #
    ccnv
    #
    cuni
    @2
    @18
    @12
    @20
    @18
    @11
    @19
    @9
    @4
    sneq
    cnveqd
    unieqd
    @1
    @0
    opswap
    syl6eq
    #
    mpt2mpt
    eqcomi
    a1i
    @21
    fmpt2co
    trud
    vx
    vy
    vz
    cX
    cY
    @9
    @2
    @9
    @2
    wceq
    id
    mpt2mpt
    vz
    @8
    mptresid
    3eqtr2i
end
