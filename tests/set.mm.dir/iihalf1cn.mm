include "cc0.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cicc.mm"
include "cv.mm"
include "cmul.mm"
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
include "0re.mm"
include "halfre.mm"
include "iccssre.mm"
include "mp2an.mm"
include "a1i.mm"
include "unitssre.mm"
include "iihalf1.mm"
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
include "cnmptre.mm"
include "trud.mm"

theorem iihalf1cn
  let vx: setvar x
  let cJ: class J
  assume iihalf1cn.1: |- J = ( ( topGen ` ran (,) ) |`t ( 0 [,] ( 1 / 2 ) ) )


  assert |- ( x e. ( 0 [,] ( 1 / 2 ) ) |-> ( 2 x. x ) ) e. ( J Cn II )

  proof
    vx
    cc0
    c1
    c2
    cdiv
    co
    #
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
    @3
    cJ
    cii
    @5
    eqid
    #
    iihalf1cn.1
    dfii2
    @1
    cr
    wss
    #
    wtru
    cc0
    cr
    wcel
    @0
    cr
    wcel
    @7
    0re
    halfre
    cc0
    @0
    iccssre
    mp2an
    a1i
    @4
    cr
    wss
    wtru
    unitssre
    a1i
    @2
    @1
    wcel
    @3
    @4
    wcel
    wtru
    @2
    iihalf1
    adantl
    wtru
    vx
    c2
    @2
    cmul
    @5
    @5
    @5
    @5
    cc
    @5
    cc
    ctopon
    cfv
    wcel
    wtru
    @5
    @6
    cnfldtopon
    a1i
    #
    wtru
    vx
    c2
    @5
    @5
    cc
    cc
    @8
    @8
    wtru
    2cnd
    cnmptc
    wtru
    vx
    @5
    cc
    @8
    cnmptid
    cmul
    @5
    @5
    ctx
    co
    @5
    ccn
    co
    wcel
    wtru
    @5
    @6
    mulcn
    a1i
    cnmpt12f
    cnmptre
    trud
end
