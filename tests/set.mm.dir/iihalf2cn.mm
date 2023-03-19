include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cicc.mm"
include "cv.mm"
include "cmul.mm"
include "cmin.mm"
include "cmpt.mm"
include "cii.mm"
include "ccn.mm"
include "wcel.mm"
include "wtru.mm"
include "cc0.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "eqid.mm"
include "dfii2.mm"
include "cr.mm"
include "wss.mm"
include "halfre.mm"
include "1re.mm"
include "iccssre.mm"
include "mp2an.mm"
include "a1i.mm"
include "unitssre.mm"
include "iihalf2.mm"
include "adantl.mm"
include "cc.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "2cnd.mm"
include "cnmptc.mm"
include "cnmptid.mm"
include "ctx.mm"
include "mulcn.mm"
include "cnmpt12f.mm"
include "1cnd.mm"
include "subcn.mm"
include "cnmptre.mm"
include "trud.mm"

theorem iihalf2cn
  let vx: setvar x
  let cJ: class J
  assume iihalf2cn.1: |- J = ( ( topGen ` ran (,) ) |`t ( ( 1 / 2 ) [,] 1 ) )


  assert |- ( x e. ( ( 1 / 2 ) [,] 1 ) |-> ( ( 2 x. x ) - 1 ) ) e. ( J Cn II )

  proof
    vx
    c1
    c2
    cdiv
    co
    #
    c1
    cicc
    co
    #
    c2
    vx
    cv
    #
    cmul
    co
    #
    c1
    cmin
    co
    #
    cmpt
    cJ
    cii
    ccn
    co
    wcel
    wtru
    vx
    @1
    cc0
    c1
    cicc
    co
    #
    ccnfld
    ctopn
    cfv
    #
    @4
    cJ
    cii
    @6
    eqid
    #
    iihalf2cn.1
    dfii2
    @1
    cr
    wss
    #
    wtru
    @0
    cr
    wcel
    c1
    cr
    wcel
    @8
    halfre
    1re
    @0
    c1
    iccssre
    mp2an
    a1i
    @5
    cr
    wss
    wtru
    unitssre
    a1i
    @2
    @1
    wcel
    @4
    @5
    wcel
    wtru
    @2
    iihalf2
    adantl
    wtru
    vx
    @3
    c1
    cmin
    @6
    @6
    @6
    @6
    cc
    @6
    cc
    ctopon
    cfv
    wcel
    wtru
    @6
    @7
    cnfldtopon
    a1i
    #
    wtru
    vx
    c2
    @2
    cmul
    @6
    @6
    @6
    @6
    cc
    @9
    wtru
    vx
    c2
    @6
    @6
    cc
    cc
    @9
    @9
    wtru
    2cnd
    cnmptc
    wtru
    vx
    @6
    cc
    @9
    cnmptid
    cmul
    @6
    @6
    ctx
    co
    @6
    ccn
    co
    #
    wcel
    wtru
    @6
    @7
    mulcn
    a1i
    cnmpt12f
    wtru
    vx
    c1
    @6
    @6
    cc
    cc
    @9
    @9
    wtru
    1cnd
    cnmptc
    cmin
    @10
    wcel
    wtru
    @6
    @7
    subcn
    a1i
    cnmpt12f
    cnmptre
    trud
end
