include "c0.mm"
include "wceq.mm"
include "clmod.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cpw.mm"
include "wa.mm"
include "c0g.mm"
include "clinco.mm"
include "co.mm"
include "csn.mm"
include "fvex.mm"
include "snid.mm"
include "oveq2.mm"
include "cgrp.mm"
include "cmnd.mm"
include "lmodgrp.mm"
include "grpmnd.mm"
include "lco0.mm"
include "3syl.mm"
include "adantr.mm"
include "sylan9eq.mm"
include "syl5eleqr.mm"
include "wn.mm"
include "cv.mm"
include "csca.mm"
include "cfsupp.mm"
include "wbr.mm"
include "clinc.mm"
include "cmap.mm"
include "wrex.mm"
include "eqid.mm"
include "lmod0vcl.mm"
include "adantl.mm"
include "cmpt.mm"
include "w3a.mm"
include "eqidd.mm"
include "cbvmptv.mm"
include "lcoc0.mm"
include "wi.mm"
include "simpl.mm"
include "wb.mm"
include "breq1.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "anbi12d.mm"
include "rspcedv.mm"
include "ex.mm"
include "com23.mm"
include "3impib.mm"
include "mpcom.mm"
include "lcoval.mm"
include "mpbir2and.mm"
include "pm2.61ian.mm"

theorem lcoel0
  let cM: class M
  let cV: class V
  let vs: setvar s
  let vv: setvar v
  let vw: setvar w
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( M e. LMod /\ V e. ~P ( Base ` M ) ) -> ( 0g ` M ) e. ( M LinCo V ) )

  proof
    cV
    c0
    wceq
    #
    cM
    clmod
    wcel
    #
    cV
    cM
    cbs
    cfv
    #
    cpw
    wcel
    #
    wa
    #
    cM
    c0g
    cfv
    #
    cM
    cV
    clinco
    co
    #
    wcel
    #
    @0
    @4
    wa
    @5
    @5
    csn
    #
    @6
    @5
    cM
    c0g
    fvex
    snid
    @0
    @4
    @6
    cM
    c0
    clinco
    co
    #
    @8
    cV
    c0
    cM
    clinco
    oveq2
    @1
    @9
    @8
    wceq
    #
    @3
    @1
    cM
    cgrp
    wcel
    cM
    cmnd
    wcel
    @10
    cM
    lmodgrp
    cM
    grpmnd
    cM
    lco0
    3syl
    adantr
    sylan9eq
    syl5eleqr
    @0
    wn
    #
    @4
    wa
    #
    @7
    @5
    @2
    wcel
    #
    vs
    cv
    #
    cM
    csca
    cfv
    #
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    @5
    @14
    cV
    cM
    clinc
    cfv
    #
    co
    #
    wceq
    #
    wa
    #
    vs
    @15
    cbs
    cfv
    #
    cV
    cmap
    co
    #
    wrex
    #
    @4
    @13
    @11
    @1
    @13
    @3
    @2
    cM
    @5
    @2
    eqid
    #
    @5
    eqid
    #
    lmod0vcl
    adantr
    adantl
    vv
    cV
    @16
    cmpt
    #
    @23
    wcel
    #
    @27
    @16
    cfsupp
    wbr
    #
    @27
    cV
    @18
    co
    #
    @5
    wceq
    #
    w3a
    #
    @12
    @24
    @4
    @32
    @11
    vw
    @2
    @22
    @15
    @27
    cM
    cV
    @16
    @5
    @25
    @15
    eqid
    #
    @16
    eqid
    @26
    vv
    vw
    cV
    @16
    @16
    vv
    cv
    vw
    cv
    wceq
    @16
    eqidd
    cbvmptv
    @22
    eqid
    #
    lcoc0
    adantl
    @28
    @29
    @31
    @12
    @24
    wi
    @28
    @12
    @29
    @31
    wa
    #
    @24
    @28
    @12
    @35
    @24
    wi
    @28
    @12
    wa
    #
    @21
    @35
    vs
    @27
    @23
    @28
    @12
    simpl
    @14
    @27
    wceq
    #
    @21
    @35
    wb
    @36
    @37
    @17
    @29
    @20
    @31
    @14
    @27
    @16
    cfsupp
    breq1
    @37
    @20
    @5
    @30
    wceq
    @31
    @37
    @19
    @30
    @5
    @14
    @27
    cV
    @18
    oveq1
    eqeq2d
    @5
    @30
    eqcom
    syl6bb
    anbi12d
    adantl
    rspcedv
    ex
    com23
    3impib
    mpcom
    @4
    @7
    @13
    @24
    wa
    wb
    @11
    @2
    @5
    @22
    @15
    cM
    cV
    clmod
    vs
    @25
    @33
    @34
    lcoval
    adantl
    mpbir2and
    pm2.61ian
end
