include "ctop.mm"
include "wcel.mm"
include "ccld.mm"
include "cfv.mm"
include "cv.mm"
include "cdif.mm"
include "opncld.mm"
include "cldopn.mm"
include "adantl.mm"
include "wa.mm"
include "wceq.mm"
include "wss.mm"
include "cldss.mm"
include "ad2antll.mm"
include "dfss4.mm"
include "sylib.mm"
include "eqcomd.mm"
include "difeq2.mm"
include "eqeq2d.mm"
include "syl5ibrcom.mm"
include "eltopss.mm"
include "adantrr.mm"
include "impbid.mm"
include "f1ocnv2d.mm"

theorem opncldf1
  let vx: setvar x
  let vu: setvar u
  let cF: class F
  let cJ: class J
  let cX: class X
  let cA: class A
  let cB: class B
  assume opncldf.1: |- X = U. J
  assume opncldf.2: |- F = ( u e. J |-> ( X \ u ) )

  disjoint F x
  disjoint u x
  disjoint J u
  disjoint J x
  disjoint X u
  disjoint X x
  disjoint A u
  disjoint B x
  assert |- ( J e. Top -> ( F : J -1-1-onto-> ( Clsd ` J ) /\ `' F = ( x e. ( Clsd ` J ) |-> ( X \ x ) ) ) )

  proof
    cJ
    ctop
    wcel
    #
    vu
    vx
    cJ
    cJ
    ccld
    cfv
    #
    cX
    vu
    cv
    #
    cdif
    #
    cX
    vx
    cv
    #
    cdif
    #
    cF
    opncldf.2
    @2
    cJ
    cX
    opncldf.1
    opncld
    @4
    @1
    wcel
    #
    @5
    cJ
    wcel
    @0
    @4
    cJ
    cX
    opncldf.1
    cldopn
    adantl
    @0
    @2
    cJ
    wcel
    #
    @6
    wa
    wa
    #
    @2
    @5
    wceq
    #
    @4
    @3
    wceq
    #
    @8
    @10
    @9
    @4
    cX
    @5
    cdif
    #
    wceq
    @8
    @11
    @4
    @8
    @4
    cX
    wss
    #
    @11
    @4
    wceq
    @6
    @12
    @0
    @7
    @4
    cJ
    cX
    opncldf.1
    cldss
    ad2antll
    @4
    cX
    dfss4
    sylib
    eqcomd
    @9
    @3
    @11
    @4
    @2
    @5
    cX
    difeq2
    eqeq2d
    syl5ibrcom
    @8
    @9
    @10
    @2
    cX
    @3
    cdif
    #
    wceq
    @8
    @13
    @2
    @8
    @2
    cX
    wss
    #
    @13
    @2
    wceq
    @0
    @7
    @14
    @6
    @2
    cJ
    cX
    opncldf.1
    eltopss
    adantrr
    @2
    cX
    dfss4
    sylib
    eqcomd
    @10
    @5
    @13
    @2
    @4
    @3
    cX
    difeq2
    eqeq2d
    syl5ibrcom
    impbid
    f1ocnv2d
end
