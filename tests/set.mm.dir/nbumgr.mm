include "wcel.mm"
include "cumgr.mm"
include "cnbgr.mm"
include "co.mm"
include "cv.mm"
include "cpr.mm"
include "crab.mm"
include "wceq.mm"
include "wi.mm"
include "nbumgrvtx.mm"
include "expcom.mm"
include "wn.mm"
include "wa.mm"
include "c0.mm"
include "wnel.mm"
include "df-nel.mm"
include "nbgrnvtx0.mm"
include "sylbir.mm"
include "adantr.mm"
include "wral.mm"
include "umgrpredgv.mm"
include "simpld.mm"
include "ex.mm"
include "adantl.mm"
include "con3d.mm"
include "com13.mm"
include "imp.mm"
include "ralrimiv.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem nbumgr
  let vn: setvar n
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let ve: setvar e
  let cX: class X
  let vv: setvar v
  let vx: setvar x
  let cK: class K
  assume nbuhgr.v: |- V = ( Vtx ` G )
  assume nbuhgr.e: |- E = ( Edg ` G )

  disjoint G n
  disjoint N n
  disjoint V n
  disjoint E n
  disjoint E e
  disjoint G e
  disjoint e n
  disjoint N e
  disjoint V e
  disjoint X e
  disjoint X n
  disjoint E v
  disjoint E x
  disjoint n v
  disjoint n x
  disjoint v x
  disjoint G x
  disjoint e x
  disjoint G v
  disjoint N v
  disjoint N x
  disjoint V v
  disjoint V x
  disjoint K n
  disjoint e v
  assert |- ( G e. UMGraph -> ( G NeighbVtx N ) = { n e. V | { N , n } e. E } )

  proof
    cN
    cV
    wcel
    #
    cG
    cumgr
    wcel
    #
    cG
    cN
    cnbgr
    co
    #
    cN
    vn
    cv
    #
    cpr
    cE
    wcel
    #
    vn
    cV
    crab
    #
    wceq
    #
    wi
    @1
    @0
    @6
    vn
    cE
    cG
    cN
    cV
    nbuhgr.v
    nbuhgr.e
    nbumgrvtx
    expcom
    @0
    wn
    #
    @1
    @6
    @7
    @1
    wa
    #
    @2
    c0
    @5
    @7
    @2
    c0
    wceq
    #
    @1
    @7
    cN
    cV
    wnel
    @9
    cN
    cV
    df-nel
    cG
    cV
    cN
    nbuhgr.v
    nbgrnvtx0
    sylbir
    adantr
    @8
    @4
    wn
    #
    vn
    cV
    wral
    @5
    c0
    wceq
    @8
    @10
    vn
    cV
    @7
    @1
    @3
    cV
    wcel
    #
    @10
    wi
    @11
    @1
    @7
    @10
    @11
    @1
    @7
    @10
    wi
    @11
    @1
    wa
    @4
    @0
    @1
    @4
    @0
    wi
    @11
    @1
    @4
    @0
    @1
    @4
    wa
    @0
    @11
    cE
    cG
    cN
    @3
    cV
    nbuhgr.v
    nbuhgr.e
    umgrpredgv
    simpld
    ex
    adantl
    con3d
    ex
    com13
    imp
    ralrimiv
    @4
    vn
    cV
    rabeq0
    sylibr
    eqtr4d
    ex
    pm2.61i
end
