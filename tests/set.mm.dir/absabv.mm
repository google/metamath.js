include "cabs.mm"
include "ccnfld.mm"
include "cabv.mm"
include "cfv.mm"
include "wcel.mm"
include "wtru.mm"
include "cc.mm"
include "caddc.mm"
include "cmul.mm"
include "cc0.mm"
include "eqidd.mm"
include "cbs.mm"
include "wceq.mm"
include "cnfldbas.mm"
include "a1i.mm"
include "cplusg.mm"
include "cnfldadd.mm"
include "cmulr.mm"
include "cnfldmul.mm"
include "c0g.mm"
include "cnfld0.mm"
include "crg.mm"
include "cnring.mm"
include "cr.mm"
include "wf.mm"
include "absf.mm"
include "abs0.mm"
include "cv.mm"
include "wne.mm"
include "clt.mm"
include "wbr.mm"
include "absgt0.mm"
include "biimpa.mm"
include "3adant1.mm"
include "wa.mm"
include "co.mm"
include "absmul.mm"
include "ad2ant2r.mm"
include "cle.mm"
include "abstri.mm"
include "isabvd.mm"
include "trud.mm"

theorem absabv
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cR: class R


  assert |- abs e. ( AbsVal ` CCfld )

  proof
    cabs
    ccnfld
    cabv
    cfv
    #
    wcel
    wtru
    vx
    vy
    @0
    cc
    caddc
    ccnfld
    cmul
    cabs
    cc0
    wtru
    @0
    eqidd
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
    cc0
    ccnfld
    c0g
    cfv
    wceq
    wtru
    cnfld0
    a1i
    ccnfld
    crg
    wcel
    wtru
    cnring
    a1i
    cc
    cr
    cabs
    wf
    wtru
    absf
    a1i
    cc0
    cabs
    cfv
    cc0
    wceq
    wtru
    abs0
    a1i
    vx
    cv
    #
    cc
    wcel
    #
    @1
    cc0
    wne
    #
    cc0
    @1
    cabs
    cfv
    #
    clt
    wbr
    #
    wtru
    @2
    @3
    @5
    @1
    absgt0
    biimpa
    3adant1
    @2
    @3
    wa
    #
    vy
    cv
    #
    cc
    wcel
    #
    @7
    cc0
    wne
    #
    wa
    #
    @1
    @7
    cmul
    co
    cabs
    cfv
    @4
    @7
    cabs
    cfv
    #
    cmul
    co
    wceq
    #
    wtru
    @2
    @8
    @12
    @3
    @9
    @1
    @7
    absmul
    ad2ant2r
    3adant1
    @6
    @10
    @1
    @7
    caddc
    co
    cabs
    cfv
    @4
    @11
    caddc
    co
    cle
    wbr
    #
    wtru
    @2
    @8
    @13
    @3
    @9
    @1
    @7
    abstri
    ad2ant2r
    3adant1
    isabvd
    trud
end
