include "ccnfld.mm"
include "csr.mm"
include "wcel.mm"
include "wtru.mm"
include "caddc.mm"
include "cmul.mm"
include "ccj.mm"
include "cc.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "cnfldbas.mm"
include "a1i.mm"
include "cplusg.mm"
include "cnfldadd.mm"
include "cmulr.mm"
include "cnfldmul.mm"
include "cstv.mm"
include "cnfldcj.mm"
include "crg.mm"
include "cnring.mm"
include "cv.mm"
include "cjcl.mm"
include "adantl.mm"
include "co.mm"
include "cjadd.mm"
include "3adant1.mm"
include "wa.mm"
include "mulcom.mm"
include "fveq2d.mm"
include "cjmul.mm"
include "ancoms.mm"
include "eqtrd.mm"
include "cjcj.mm"
include "issrngd.mm"
include "trud.mm"

theorem cnsrng
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B


  assert |- CCfld e. *Ring

  proof
    ccnfld
    csr
    wcel
    wtru
    vx
    vy
    caddc
    ccnfld
    cmul
    ccj
    cc
    cc
    ccnfld
    cbs
    cfv
    wceq
    wtru
    cnfldbas
    a1i
    caddc
    ccnfld
    cplusg
    cfv
    wceq
    wtru
    cnfldadd
    a1i
    cmul
    ccnfld
    cmulr
    cfv
    wceq
    wtru
    cnfldmul
    a1i
    ccj
    ccnfld
    cstv
    cfv
    wceq
    wtru
    cnfldcj
    a1i
    ccnfld
    crg
    wcel
    wtru
    cnring
    a1i
    vx
    cv
    #
    cc
    wcel
    #
    @0
    ccj
    cfv
    #
    cc
    wcel
    wtru
    @0
    cjcl
    adantl
    @1
    vy
    cv
    #
    cc
    wcel
    #
    @0
    @3
    caddc
    co
    ccj
    cfv
    @2
    @3
    ccj
    cfv
    #
    caddc
    co
    wceq
    wtru
    @0
    @3
    cjadd
    3adant1
    @1
    @4
    @0
    @3
    cmul
    co
    #
    ccj
    cfv
    #
    @5
    @2
    cmul
    co
    #
    wceq
    wtru
    @1
    @4
    wa
    #
    @7
    @3
    @0
    cmul
    co
    #
    ccj
    cfv
    #
    @8
    @9
    @6
    @10
    ccj
    @0
    @3
    mulcom
    fveq2d
    @4
    @1
    @11
    @8
    wceq
    @3
    @0
    cjmul
    ancoms
    eqtrd
    3adant1
    @1
    @2
    ccj
    cfv
    @0
    wceq
    wtru
    @0
    cjcj
    adantl
    issrngd
    trud
end
