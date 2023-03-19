include "clmod.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cpw.mm"
include "wa.mm"
include "clinco.mm"
include "co.mm"
include "cv.mm"
include "csca.mm"
include "c0g.mm"
include "cfsupp.mm"
include "wbr.mm"
include "clinc.mm"
include "wceq.mm"
include "cmap.mm"
include "wrex.mm"
include "wi.mm"
include "elelpwi.mm"
include "expcom.mm"
include "adantl.mm"
include "imp.mm"
include "weq.mm"
include "cur.mm"
include "cif.mm"
include "cmpt.mm"
include "eqid.mm"
include "equequ1.mm"
include "ifbid.mm"
include "cbvmptv.mm"
include "mptcfsupp.mm"
include "3expa.mm"
include "linc1.mm"
include "eqcomd.mm"
include "wf.mm"
include "lmod1cl.mm"
include "lmod0cl.mm"
include "ifcld.mm"
include "ad3antrrr.mm"
include "fmptd.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "simplr.mm"
include "elmapg.mm"
include "sylancr.mm"
include "mpbird.mm"
include "breq1.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcedv.mm"
include "mp2and.mm"
include "lcoval.mm"
include "adantr.mm"
include "mpbir2and.mm"
include "ex.mm"
include "ssrdv.mm"

theorem lcoss
  let cM: class M
  let cV: class V
  let vf: setvar f
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k


  assert |- ( ( M e. LMod /\ V e. ~P ( Base ` M ) ) -> V C_ ( M LinCo V ) )

  proof
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
    #
    wcel
    #
    wa
    #
    vv
    cV
    cM
    cV
    clinco
    co
    #
    @4
    vv
    cv
    #
    cV
    wcel
    #
    @6
    @5
    wcel
    #
    @4
    @7
    wa
    #
    @8
    @6
    @1
    wcel
    #
    vf
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
    @6
    @11
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
    vf
    @12
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
    @7
    @10
    @3
    @7
    @10
    wi
    @0
    @7
    @3
    @10
    @6
    cV
    @1
    elelpwi
    expcom
    adantl
    imp
    @9
    vx
    cV
    vx
    vv
    weq
    #
    @12
    cur
    cfv
    #
    @13
    cif
    #
    cmpt
    #
    @13
    cfsupp
    wbr
    #
    @6
    @25
    cV
    @15
    co
    #
    wceq
    #
    @21
    @0
    @3
    @7
    @26
    vy
    @1
    @12
    @23
    @25
    cM
    cV
    @6
    @13
    @1
    eqid
    #
    @12
    eqid
    #
    @13
    eqid
    #
    @23
    eqid
    #
    vx
    vy
    cV
    @24
    vy
    vv
    weq
    #
    @23
    @13
    cif
    vx
    vy
    weq
    @22
    @33
    @23
    @13
    vx
    vy
    vv
    equequ1
    ifbid
    cbvmptv
    mptcfsupp
    3expa
    @9
    @27
    @6
    @0
    @3
    @7
    @27
    @6
    wceq
    vx
    @1
    @12
    @23
    @25
    cM
    cV
    @6
    @13
    @29
    @30
    @31
    @32
    @25
    eqid
    #
    linc1
    3expa
    eqcomd
    @9
    @18
    @26
    @28
    wa
    #
    vf
    @25
    @20
    @9
    @25
    @20
    wcel
    #
    cV
    @19
    @25
    wf
    #
    @9
    vx
    cV
    @24
    @19
    @25
    @0
    @24
    @19
    wcel
    @3
    @7
    vx
    cv
    cV
    wcel
    @0
    @22
    @23
    @13
    @19
    @23
    @12
    @19
    cM
    @30
    @19
    eqid
    #
    @32
    lmod1cl
    @12
    @19
    cM
    @13
    @30
    @38
    @31
    lmod0cl
    ifcld
    ad3antrrr
    @34
    fmptd
    @9
    @19
    cvv
    wcel
    @3
    @36
    @37
    wb
    @12
    cbs
    fvex
    @0
    @3
    @7
    simplr
    @19
    cV
    @25
    cvv
    @2
    elmapg
    sylancr
    mpbird
    @11
    @25
    wceq
    #
    @18
    @35
    wb
    @9
    @39
    @14
    @26
    @17
    @28
    @11
    @25
    @13
    cfsupp
    breq1
    @39
    @16
    @27
    @6
    @11
    @25
    cV
    @15
    oveq1
    eqeq2d
    anbi12d
    adantl
    rspcedv
    mp2and
    @4
    @8
    @10
    @21
    wa
    wb
    @7
    @1
    @6
    @19
    @12
    cM
    cV
    clmod
    vf
    @29
    @30
    @38
    lcoval
    adantr
    mpbir2and
    ex
    ssrdv
end
