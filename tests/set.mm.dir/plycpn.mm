include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cc.mm"
include "ccpn.mm"
include "crn.mm"
include "cint.mm"
include "cv.mm"
include "wral.mm"
include "cn0.mm"
include "wa.mm"
include "cpm.mm"
include "co.mm"
include "cdvn.mm"
include "cdm.mm"
include "ccncf.mm"
include "wf.mm"
include "plyf.mm"
include "adantr.mm"
include "cnex.mm"
include "fpm.mm"
include "syl.mm"
include "dvnply.mm"
include "plycn.mm"
include "wceq.mm"
include "fdm.mm"
include "oveq1d.mm"
include "eleqtrrd.mm"
include "wss.mm"
include "wb.mm"
include "ssid.mm"
include "a1i.mm"
include "elcpn.mm"
include "sylan.mm"
include "mpbir2and.mm"
include "ralrimiva.mm"
include "wfn.mm"
include "fncpn.mm"
include "eleq2.mm"
include "ralrn.mm"
include "mp2b.mm"
include "sylibr.mm"
include "elintg.mm"
include "mpbird.mm"

theorem plycpn
  let cS: class S
  let cF: class F
  let vn: setvar n
  let vx: setvar x
  let cN: class N


  assert |- ( F e. ( Poly ` S ) -> F e. |^| ran ( C^n ` CC ) )

  proof
    cF
    cS
    cply
    cfv
    #
    wcel
    #
    cF
    cc
    ccpn
    cfv
    #
    crn
    #
    cint
    wcel
    cF
    vx
    cv
    #
    wcel
    #
    vx
    @3
    wral
    #
    @1
    cF
    vn
    cv
    #
    @2
    cfv
    #
    wcel
    #
    vn
    cn0
    wral
    #
    @6
    @1
    @9
    vn
    cn0
    @1
    @7
    cn0
    wcel
    #
    wa
    #
    @9
    cF
    cc
    cc
    cpm
    co
    wcel
    #
    @7
    cc
    cF
    cdvn
    co
    cfv
    #
    cF
    cdm
    #
    cc
    ccncf
    co
    #
    wcel
    #
    @12
    cc
    cc
    cF
    wf
    #
    @13
    @1
    @18
    @11
    cS
    cF
    plyf
    adantr
    #
    cc
    cc
    cF
    cnex
    cnex
    fpm
    syl
    @12
    @14
    cc
    cc
    ccncf
    co
    #
    @16
    @12
    @14
    cc
    cply
    cfv
    wcel
    @14
    @20
    wcel
    cS
    cF
    @7
    dvnply
    cc
    @14
    plycn
    syl
    @12
    @15
    cc
    cc
    ccncf
    @12
    @18
    @15
    cc
    wceq
    @19
    cc
    cc
    cF
    fdm
    syl
    oveq1d
    eleqtrrd
    @1
    cc
    cc
    wss
    #
    @11
    @9
    @13
    @17
    wa
    wb
    @21
    @1
    cc
    ssid
    #
    a1i
    cc
    cF
    @7
    elcpn
    sylan
    mpbir2and
    ralrimiva
    @21
    @2
    cn0
    wfn
    @6
    @10
    wb
    @22
    cc
    fncpn
    @5
    @9
    vx
    vn
    cn0
    @2
    @4
    @8
    cF
    eleq2
    ralrn
    mp2b
    sylibr
    vx
    cF
    @3
    @0
    elintg
    mpbird
end
