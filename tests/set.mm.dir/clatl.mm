include "cpo.mm"
include "wcel.mm"
include "club.mm"
include "cfv.mm"
include "cdm.mm"
include "cbs.mm"
include "cpw.mm"
include "wceq.mm"
include "cglb.mm"
include "wa.mm"
include "cjn.mm"
include "cxp.mm"
include "cmee.mm"
include "ccla.mm"
include "clat.mm"
include "eqid.mm"
include "simpl.mm"
include "joindmss.mm"
include "wrel.mm"
include "relxp.mm"
include "a1i.mm"
include "cv.mm"
include "cop.mm"
include "cpr.mm"
include "wi.mm"
include "wss.mm"
include "opelxp.mm"
include "vex.mm"
include "prss.mm"
include "sylbb.mm"
include "prex.mm"
include "elpw.mm"
include "sylibr.mm"
include "eleq2.mm"
include "syl5ibr.mm"
include "adantl.mm"
include "cvv.mm"
include "joindef.mm"
include "sylibrd.mm"
include "relssdv.mm"
include "eqssd.mm"
include "ex.mm"
include "meetdmss.mm"
include "meetdef.mm"
include "anim12d.mm"
include "imdistani.mm"
include "isclat.mm"
include "islat.mm"
include "3imtr4i.mm"

theorem clatl
  let cK: class K
  let vx: setvar x
  let vy: setvar y


  assert |- ( K e. CLat -> K e. Lat )

  proof
    cK
    cpo
    wcel
    #
    cK
    club
    cfv
    #
    cdm
    #
    cK
    cbs
    cfv
    #
    cpw
    #
    wceq
    #
    cK
    cglb
    cfv
    #
    cdm
    #
    @4
    wceq
    #
    wa
    #
    wa
    @0
    cK
    cjn
    cfv
    #
    cdm
    #
    @3
    @3
    cxp
    #
    wceq
    #
    cK
    cmee
    cfv
    #
    cdm
    #
    @12
    wceq
    #
    wa
    #
    wa
    cK
    ccla
    wcel
    cK
    clat
    wcel
    @0
    @9
    @17
    @0
    @5
    @13
    @8
    @16
    @0
    @5
    @13
    @0
    @5
    wa
    #
    @11
    @12
    @18
    @3
    @10
    cK
    cpo
    @3
    eqid
    #
    @10
    eqid
    #
    @0
    @5
    simpl
    #
    joindmss
    @18
    vx
    vy
    @12
    @11
    @12
    wrel
    #
    @18
    @3
    @3
    relxp
    #
    a1i
    @18
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    @12
    wcel
    #
    @24
    @25
    cpr
    #
    @2
    wcel
    #
    @26
    @11
    wcel
    @5
    @27
    @29
    wi
    @0
    @27
    @29
    @5
    @28
    @4
    wcel
    #
    @27
    @28
    @3
    wss
    #
    @30
    @27
    @24
    @3
    wcel
    @25
    @3
    wcel
    wa
    @31
    @24
    @25
    @3
    @3
    opelxp
    @24
    @25
    @3
    vx
    vex
    #
    vy
    vex
    #
    prss
    sylbb
    @28
    @3
    @24
    @25
    prex
    elpw
    sylibr
    #
    @2
    @4
    @28
    eleq2
    syl5ibr
    adantl
    @18
    @1
    @10
    cK
    cpo
    cvv
    @24
    @25
    cvv
    @1
    eqid
    #
    @20
    @21
    @24
    cvv
    wcel
    #
    @18
    @32
    a1i
    @25
    cvv
    wcel
    #
    @18
    @33
    a1i
    joindef
    sylibrd
    relssdv
    eqssd
    ex
    @0
    @8
    @16
    @0
    @8
    wa
    #
    @15
    @12
    @38
    @3
    cK
    @14
    cpo
    @19
    @14
    eqid
    #
    @0
    @8
    simpl
    #
    meetdmss
    @38
    vx
    vy
    @12
    @15
    @22
    @38
    @23
    a1i
    @38
    @27
    @28
    @7
    wcel
    #
    @26
    @15
    wcel
    @8
    @27
    @41
    wi
    @0
    @27
    @41
    @8
    @30
    @34
    @7
    @4
    @28
    eleq2
    syl5ibr
    adantl
    @38
    @6
    cK
    @14
    cpo
    cvv
    @24
    @25
    cvv
    @6
    eqid
    #
    @39
    @40
    @36
    @38
    @32
    a1i
    @37
    @38
    @33
    a1i
    meetdef
    sylibrd
    relssdv
    eqssd
    ex
    anim12d
    imdistani
    @3
    @1
    @6
    cK
    @19
    @35
    @42
    isclat
    @3
    @10
    cK
    @14
    @19
    @20
    @39
    islat
    3imtr4i
end
