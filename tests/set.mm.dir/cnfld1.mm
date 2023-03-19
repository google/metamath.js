include "ccnfld.mm"
include "cur.mm"
include "cfv.mm"
include "c1.mm"
include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "ax-1cn.mm"
include "mulid2.mm"
include "mulid1.mm"
include "jca.mm"
include "rgen.mm"
include "pm3.2i.mm"
include "crg.mm"
include "wb.mm"
include "cnring.mm"
include "cnfldbas.mm"
include "cnfldmul.mm"
include "eqid.mm"
include "isringid.mm"
include "ax-mp.mm"
include "mpbi.mm"
include "eqcomi.mm"

theorem cnfld1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B


  assert |- 1 = ( 1r ` CCfld )

  proof
    ccnfld
    cur
    cfv
    #
    c1
    c1
    cc
    wcel
    #
    c1
    vx
    cv
    #
    cmul
    co
    @2
    wceq
    #
    @2
    c1
    cmul
    co
    @2
    wceq
    #
    wa
    #
    vx
    cc
    wral
    #
    wa
    #
    @0
    c1
    wceq
    #
    @1
    @6
    ax-1cn
    @5
    vx
    cc
    @2
    cc
    wcel
    @3
    @4
    @2
    mulid2
    @2
    mulid1
    jca
    rgen
    pm3.2i
    ccnfld
    crg
    wcel
    @7
    @8
    wb
    cnring
    vx
    cc
    ccnfld
    cmul
    @0
    c1
    cnfldbas
    cnfldmul
    @0
    eqid
    isringid
    ax-mp
    mpbi
    eqcomi
end
