include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "cmin.mm"
include "cmpt.mm"
include "cii.mm"
include "ccn.mm"
include "wcel.mm"
include "wtru.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "eqid.mm"
include "dfii2.mm"
include "cr.mm"
include "wss.mm"
include "unitssre.mm"
include "a1i.mm"
include "iirev.mm"
include "adantl.mm"
include "cc.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "1cnd.mm"
include "cnmptc.mm"
include "cnmptid.mm"
include "ctx.mm"
include "subcn.mm"
include "cnmpt12f.mm"
include "cnmptre.mm"
include "trud.mm"

theorem iirevcn
  let vx: setvar x


  assert |- ( x e. ( 0 [,] 1 ) |-> ( 1 - x ) ) e. ( II Cn II )

  proof
    vx
    cc0
    c1
    cicc
    co
    #
    c1
    vx
    cv
    #
    cmin
    co
    #
    cmpt
    cii
    cii
    ccn
    co
    wcel
    wtru
    vx
    @0
    @0
    ccnfld
    ctopn
    cfv
    #
    @2
    cii
    cii
    @3
    eqid
    #
    dfii2
    dfii2
    @0
    cr
    wss
    wtru
    unitssre
    a1i
    #
    @5
    @1
    @0
    wcel
    @2
    @0
    wcel
    wtru
    @1
    iirev
    adantl
    wtru
    vx
    c1
    @1
    cmin
    @3
    @3
    @3
    @3
    cc
    @3
    cc
    ctopon
    cfv
    wcel
    wtru
    @3
    @4
    cnfldtopon
    a1i
    #
    wtru
    vx
    c1
    @3
    @3
    cc
    cc
    @6
    @6
    wtru
    1cnd
    cnmptc
    wtru
    vx
    @3
    cc
    @6
    cnmptid
    cmin
    @3
    @3
    ctx
    co
    @3
    ccn
    co
    wcel
    wtru
    @3
    @4
    subcn
    a1i
    cnmpt12f
    cnmptre
    trud
end
