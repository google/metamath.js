include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "cmpt.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "crest.mm"
include "ccn.mm"
include "ccncf.mm"
include "ctopon.mm"
include "wss.mm"
include "eqid.mm"
include "cnfldtopon.mm"
include "a1i.mm"
include "difss.mm"
include "resttopon.mm"
include "sylancl.mm"
include "id.mm"
include "cnmptc.mm"
include "cnmptid.mm"
include "ctx.mm"
include "divcn.mm"
include "cnmpt12f.mm"
include "wceq.mm"
include "ssid.mm"
include "toponunii.mm"
include "restid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "cncfcn.mm"
include "mp2an.mm"
include "3eltr4g.mm"

theorem cdivcncf
  let vx: setvar x
  let cA: class A
  let cF: class F
  assume cdivcncf.1: |- F = ( x e. ( CC \ { 0 } ) |-> ( A / x ) )

  disjoint A x
  assert |- ( A e. CC -> F e. ( ( CC \ { 0 } ) -cn-> CC ) )

  proof
    cA
    cc
    wcel
    #
    vx
    cc
    cc0
    csn
    #
    cdif
    #
    cA
    vx
    cv
    #
    cdiv
    co
    cmpt
    ccnfld
    ctopn
    cfv
    #
    @2
    crest
    co
    #
    @4
    ccn
    co
    #
    cF
    @2
    cc
    ccncf
    co
    #
    @0
    vx
    cA
    @3
    cdiv
    @5
    @4
    @5
    @4
    @2
    @0
    @4
    cc
    ctopon
    cfv
    #
    wcel
    #
    @2
    cc
    wss
    #
    @5
    @2
    ctopon
    cfv
    wcel
    @9
    @0
    @4
    @4
    eqid
    #
    cnfldtopon
    #
    a1i
    #
    cc
    @1
    difss
    #
    @2
    @4
    cc
    resttopon
    sylancl
    #
    @0
    vx
    cA
    @5
    @4
    @2
    cc
    @15
    @13
    @0
    id
    cnmptc
    @0
    vx
    @5
    @2
    @15
    cnmptid
    cdiv
    @4
    @5
    ctx
    co
    @4
    ccn
    co
    wcel
    @0
    @4
    @5
    @11
    @5
    eqid
    #
    divcn
    a1i
    cnmpt12f
    cdivcncf.1
    @10
    cc
    cc
    wss
    @7
    @6
    wceq
    @14
    cc
    ssid
    @2
    cc
    @4
    @5
    @4
    @11
    @16
    @4
    cc
    crest
    co
    #
    @4
    @9
    @17
    @4
    wceq
    @12
    @4
    @8
    cc
    cc
    @4
    @12
    toponunii
    restid
    ax-mp
    eqcomi
    cncfcn
    mp2an
    3eltr4g
end
