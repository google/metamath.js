include "c0.mm"
include "cpr.mm"
include "cpconn.mm"
include "wcel.mm"
include "ctop.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "wa.mm"
include "cii.mm"
include "ccn.mm"
include "co.mm"
include "wrex.mm"
include "cuni.mm"
include "wral.mm"
include "indistop.mm"
include "cicc.mm"
include "cif.mm"
include "cmpt.mm"
include "cmap.mm"
include "wf.mm"
include "simpl.mm"
include "cun.mm"
include "cvv.mm"
include "0ex.mm"
include "n0i.mm"
include "wn.mm"
include "csn.mm"
include "prprc2.mm"
include "unieqd.mm"
include "unisn.mm"
include "syl6eq.mm"
include "nsyl2.mm"
include "adantr.mm"
include "uniprg.mm"
include "sylancr.mm"
include "uncom.mm"
include "un0.mm"
include "eqtri.mm"
include "eleqtrd.mm"
include "simpr.mm"
include "ifcld.mm"
include "eqid.mm"
include "fmptd.mm"
include "wb.mm"
include "ovex.mm"
include "elmapg.mm"
include "sylancl.mm"
include "mpbird.mm"
include "ctopon.mm"
include "iitopon.mm"
include "cnindis.mm"
include "eleqtrrd.mm"
include "0elunit.mm"
include "iftrue.mm"
include "vex.mm"
include "fvmpt.mm"
include "mp1i.mm"
include "1elunit.mm"
include "wne.mm"
include "ax-1ne0.mm"
include "neeq1.mm"
include "mpbiri.mm"
include "ifnefalse.mm"
include "syl.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "rgen2a.mm"
include "ispconn.mm"
include "mpbir2an.mm"

theorem indispconn
  let cA: class A
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vg: setvar g
  let vh: setvar h
  let vs: setvar s
  let vu: setvar u
  let vw: setvar w
  let cJ: class J


  assert |- { (/) , A } e. PConn

  proof
    c0
    cA
    cpr
    #
    cpconn
    wcel
    @0
    ctop
    wcel
    cc0
    vf
    cv
    #
    cfv
    #
    vx
    cv
    #
    wceq
    #
    c1
    @1
    cfv
    #
    vy
    cv
    #
    wceq
    #
    wa
    #
    vf
    cii
    @0
    ccn
    co
    #
    wrex
    #
    vy
    @0
    cuni
    #
    wral
    vx
    @11
    wral
    cA
    indistop
    @10
    vx
    vy
    @11
    @3
    @11
    wcel
    #
    @6
    @11
    wcel
    #
    wa
    #
    vz
    cc0
    c1
    cicc
    co
    #
    vz
    cv
    #
    cc0
    wceq
    #
    @3
    @6
    cif
    #
    cmpt
    #
    @9
    wcel
    cc0
    @19
    cfv
    #
    @3
    wceq
    #
    c1
    @19
    cfv
    #
    @6
    wceq
    #
    @10
    @14
    @19
    cA
    @15
    cmap
    co
    #
    @9
    @14
    @19
    @24
    wcel
    #
    @15
    cA
    @19
    wf
    #
    @14
    vz
    @15
    @18
    cA
    @19
    @14
    @18
    cA
    wcel
    @16
    @15
    wcel
    @14
    @17
    @3
    @6
    cA
    @14
    @3
    @11
    cA
    @12
    @13
    simpl
    @14
    @11
    c0
    cA
    cun
    #
    cA
    @14
    c0
    cvv
    wcel
    cA
    cvv
    wcel
    #
    @11
    @27
    wceq
    0ex
    @12
    @28
    @13
    @12
    @11
    c0
    wceq
    @28
    @11
    @3
    n0i
    @28
    wn
    #
    @11
    c0
    csn
    #
    cuni
    c0
    @29
    @0
    @30
    c0
    cA
    prprc2
    unieqd
    c0
    0ex
    unisn
    syl6eq
    nsyl2
    adantr
    #
    c0
    cA
    cvv
    cvv
    uniprg
    sylancr
    @27
    cA
    c0
    cun
    cA
    c0
    cA
    uncom
    cA
    un0
    eqtri
    syl6eq
    #
    eleqtrd
    @14
    @6
    @11
    cA
    @12
    @13
    simpr
    @32
    eleqtrd
    ifcld
    adantr
    @19
    eqid
    #
    fmptd
    @14
    @28
    @15
    cvv
    wcel
    @25
    @26
    wb
    @31
    cc0
    c1
    cicc
    ovex
    cA
    @15
    @19
    cvv
    cvv
    elmapg
    sylancl
    mpbird
    @14
    cii
    @15
    ctopon
    cfv
    wcel
    @28
    @9
    @24
    wceq
    iitopon
    @31
    cA
    cii
    cvv
    @15
    cnindis
    sylancr
    eleqtrrd
    cc0
    @15
    wcel
    @21
    @14
    0elunit
    vz
    cc0
    @18
    @3
    @15
    @19
    @17
    @3
    @6
    iftrue
    @33
    vx
    vex
    fvmpt
    mp1i
    c1
    @15
    wcel
    @23
    @14
    1elunit
    vz
    c1
    @18
    @6
    @15
    @19
    @16
    c1
    wceq
    #
    @16
    cc0
    wne
    #
    @18
    @6
    wceq
    @34
    @35
    c1
    cc0
    wne
    ax-1ne0
    @16
    c1
    cc0
    neeq1
    mpbiri
    @16
    cc0
    @3
    @6
    ifnefalse
    syl
    @33
    vy
    vex
    fvmpt
    mp1i
    @8
    @21
    @23
    wa
    vf
    @19
    @9
    @1
    @19
    wceq
    #
    @4
    @21
    @7
    @23
    @36
    @2
    @20
    @3
    cc0
    @1
    @19
    fveq1
    eqeq1d
    @36
    @5
    @22
    @6
    c1
    @1
    @19
    fveq1
    eqeq1d
    anbi12d
    rspcev
    syl12anc
    rgen2a
    vx
    vy
    vf
    @0
    @11
    @11
    eqid
    ispconn
    mpbir2an
end
