include "ccnfld.mm"
include "cdr.mm"
include "wcel.mm"
include "wtru.mm"
include "cc.mm"
include "cmul.mm"
include "c1.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "cc0.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "cnfldbas.mm"
include "a1i.mm"
include "cmulr.mm"
include "cnfldmul.mm"
include "c0g.mm"
include "cnfld0.mm"
include "cur.mm"
include "cnfld1.mm"
include "crg.mm"
include "cnring.mm"
include "wne.mm"
include "wa.mm"
include "mulne0.mm"
include "3adant1.mm"
include "ax-1ne0.mm"
include "reccl.mm"
include "adantl.mm"
include "recne0.mm"
include "recid2.mm"
include "isdrngd.mm"
include "trud.mm"

theorem cndrng
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B


  assert |- CCfld e. DivRing

  proof
    ccnfld
    cdr
    wcel
    wtru
    vx
    vy
    cc
    ccnfld
    cmul
    c1
    c1
    vx
    cv
    #
    cdiv
    co
    #
    cc0
    cc
    ccnfld
    cbs
    cfv
    wceq
    wtru
    cnfldbas
    a1i
    cmul
    ccnfld
    cmulr
    cfv
    wceq
    wtru
    cnfldmul
    a1i
    cc0
    ccnfld
    c0g
    cfv
    wceq
    wtru
    cnfld0
    a1i
    c1
    ccnfld
    cur
    cfv
    wceq
    wtru
    cnfld1
    a1i
    ccnfld
    crg
    wcel
    wtru
    cnring
    a1i
    @0
    cc
    wcel
    @0
    cc0
    wne
    wa
    #
    vy
    cv
    #
    cc
    wcel
    @3
    cc0
    wne
    wa
    @0
    @3
    cmul
    co
    cc0
    wne
    wtru
    @0
    @3
    mulne0
    3adant1
    c1
    cc0
    wne
    wtru
    ax-1ne0
    a1i
    @2
    @1
    cc
    wcel
    wtru
    @0
    reccl
    adantl
    @2
    @1
    cc0
    wne
    wtru
    @0
    recne0
    adantl
    @2
    @1
    @0
    cmul
    co
    c1
    wceq
    wtru
    @0
    recid2
    adantl
    isdrngd
    trud
end
