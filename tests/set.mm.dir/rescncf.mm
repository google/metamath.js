include "wss.mm"
include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "cres.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "simpr.mm"
include "cc.mm"
include "wb.mm"
include "cncfrss.mm"
include "adantl.mm"
include "cncfrss2.mm"
include "elcncf.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simpld.mm"
include "simpl.mm"
include "fssresd.mm"
include "simprd.mm"
include "ssralv.mm"
include "fvres.mm"
include "oveqan12d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "imbi2d.mm"
include "biimprd.mm"
include "ralimdva.mm"
include "sylan9.mm"
include "reximdv.mm"
include "ralimdv.mm"
include "syld.mm"
include "sylc.mm"
include "sstrd.mm"
include "mpbir2and.mm"
include "ex.mm"

theorem rescncf
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vf: setvar f
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( C C_ A -> ( F e. ( A -cn-> B ) -> ( F |` C ) e. ( C -cn-> B ) ) )

  proof
    cC
    cA
    wss
    #
    cF
    cA
    cB
    ccncf
    co
    wcel
    #
    cF
    cC
    cres
    #
    cC
    cB
    ccncf
    co
    wcel
    #
    @0
    @1
    wa
    #
    @3
    cC
    cB
    @2
    wf
    #
    vx
    cv
    #
    vw
    cv
    #
    cmin
    co
    cabs
    cfv
    vz
    cv
    clt
    wbr
    #
    @6
    @2
    cfv
    #
    @7
    @2
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    wi
    #
    vw
    cC
    wral
    #
    vz
    crp
    wrex
    #
    vy
    crp
    wral
    #
    vx
    cC
    wral
    #
    @4
    cA
    cB
    cC
    cF
    @4
    cA
    cB
    cF
    wf
    #
    @8
    @6
    cF
    cfv
    #
    @7
    cF
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @13
    clt
    wbr
    #
    wi
    #
    vw
    cA
    wral
    #
    vz
    crp
    wrex
    #
    vy
    crp
    wral
    #
    vx
    cA
    wral
    #
    @4
    @1
    @20
    @30
    wa
    #
    @0
    @1
    simpr
    @4
    cA
    cc
    wss
    #
    cB
    cc
    wss
    #
    @1
    @31
    wb
    @1
    @32
    @0
    cA
    cB
    cF
    cncfrss
    adantl
    #
    @1
    @33
    @0
    cA
    cB
    cF
    cncfrss2
    adantl
    #
    vx
    vy
    vz
    vw
    cA
    cB
    cF
    elcncf
    syl2anc
    mpbid
    #
    simpld
    @0
    @1
    simpl
    #
    fssresd
    @4
    @0
    @30
    @19
    @37
    @4
    @20
    @30
    @36
    simprd
    @0
    @30
    @29
    vx
    cC
    wral
    @19
    @29
    vx
    cC
    cA
    ssralv
    @0
    @29
    @18
    vx
    cC
    @0
    @6
    cC
    wcel
    #
    wa
    #
    @28
    @17
    vy
    crp
    @39
    @27
    @16
    vz
    crp
    @0
    @27
    @26
    vw
    cC
    wral
    @38
    @16
    @26
    vw
    cC
    cA
    ssralv
    @38
    @26
    @15
    vw
    cC
    @38
    @7
    cC
    wcel
    #
    wa
    #
    @15
    @26
    @41
    @14
    @25
    @8
    @41
    @12
    @24
    @13
    clt
    @41
    @11
    @23
    cabs
    @38
    @40
    @9
    @21
    @10
    @22
    cmin
    @6
    cC
    cF
    fvres
    @7
    cC
    cF
    fvres
    oveqan12d
    fveq2d
    breq1d
    imbi2d
    biimprd
    ralimdva
    sylan9
    reximdv
    ralimdv
    ralimdva
    syld
    sylc
    @4
    cC
    cc
    wss
    @33
    @3
    @5
    @19
    wa
    wb
    @4
    cC
    cA
    cc
    @37
    @34
    sstrd
    @35
    vx
    vy
    vz
    vw
    cC
    cB
    @2
    elcncf
    syl2anc
    mpbir2and
    ex
end
