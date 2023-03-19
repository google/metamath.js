include "cxp.mm"
include "wf.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "w3a.mm"
include "cmap.mm"
include "co.mm"
include "ccur.mm"
include "cv.mm"
include "cop.mm"
include "cfv.mm"
include "cmpt.mm"
include "wa.mm"
include "opelxpi.mm"
include "ffvelrn.mm"
include "sylan2.mm"
include "anassrs.mm"
include "eqid.mm"
include "fmptd.mm"
include "3ad2antl1.mm"
include "wb.mm"
include "elmapg.mm"
include "ancoms.mm"
include "3adant1.mm"
include "adantr.mm"
include "mpbird.mm"
include "wne.mm"
include "eldifsni.mm"
include "cdm.mm"
include "wbr.mm"
include "copab.mm"
include "df-cur.mm"
include "fdm.mm"
include "dmeqd.mm"
include "dmxp.mm"
include "sylan9eq.mm"
include "mpteq1d.mm"
include "wceq.mm"
include "wfun.mm"
include "ffun.mm"
include "funbrfv2b.mm"
include "syl.mm"
include "eleq2d.mm"
include "opelxp.mm"
include "syl6bb.mm"
include "anbi1d.mm"
include "bitrd.mm"
include "ibar.mm"
include "anass.mm"
include "eqcom.mm"
include "anbi2i.mm"
include "bitr3i.mm"
include "syl6rbb.mm"
include "sylan9bb.mm"
include "opabbidv.mm"
include "df-mpt.mm"
include "syl6eqr.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "feq1d.mm"
include "3adant3.mm"

theorem curf
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  let cW: class W
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( F : ( A X. B ) --> C /\ B e. ( V \ { (/) } ) /\ C e. W ) -> curry F : A --> ( C ^m B ) )

  proof
    cA
    cB
    cxp
    #
    cC
    cF
    wf
    #
    cB
    cV
    c0
    csn
    cdif
    #
    wcel
    #
    cC
    cW
    wcel
    #
    w3a
    #
    cA
    cC
    cB
    cmap
    co
    #
    cF
    ccur
    #
    wf
    #
    cA
    @6
    vx
    cA
    vy
    cB
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    cF
    cfv
    #
    cmpt
    #
    cmpt
    #
    wf
    #
    @5
    vx
    cA
    @13
    @6
    @14
    @5
    @9
    cA
    wcel
    #
    wa
    @13
    @6
    wcel
    #
    cB
    cC
    @13
    wf
    #
    @1
    @3
    @16
    @18
    @4
    @1
    @16
    wa
    #
    vy
    cB
    @12
    cC
    @13
    @1
    @16
    @10
    cB
    wcel
    #
    @12
    cC
    wcel
    #
    @16
    @20
    wa
    #
    @1
    @11
    @0
    wcel
    #
    @21
    @9
    @10
    cA
    cB
    opelxpi
    @0
    cC
    @11
    cF
    ffvelrn
    sylan2
    anassrs
    @13
    eqid
    fmptd
    3ad2antl1
    @5
    @17
    @18
    wb
    #
    @16
    @3
    @4
    @24
    @1
    @4
    @3
    @24
    cC
    cB
    @13
    cW
    @2
    elmapg
    ancoms
    3adant1
    adantr
    mpbird
    @14
    eqid
    fmptd
    @1
    @3
    @8
    @15
    wb
    #
    @4
    @3
    @1
    cB
    c0
    wne
    #
    @25
    cB
    cV
    c0
    eldifsni
    @1
    @26
    wa
    #
    cA
    @6
    @7
    @14
    @27
    @7
    vx
    cF
    cdm
    #
    cdm
    #
    @11
    vz
    cv
    #
    cF
    wbr
    #
    vy
    vz
    copab
    #
    cmpt
    #
    @14
    vx
    vy
    vz
    cF
    df-cur
    @27
    @33
    vx
    cA
    @32
    cmpt
    #
    @14
    @27
    vx
    @29
    cA
    @32
    @1
    @26
    @29
    @0
    cdm
    cA
    @1
    @28
    @0
    @0
    cC
    cF
    fdm
    #
    dmeqd
    cA
    cB
    dmxp
    sylan9eq
    mpteq1d
    @1
    @34
    @14
    wceq
    @26
    @1
    vx
    cA
    @32
    @13
    @19
    @32
    @20
    @30
    @12
    wceq
    #
    wa
    #
    vy
    vz
    copab
    @13
    @19
    @31
    @37
    vy
    vz
    @1
    @31
    @22
    @12
    @30
    wceq
    #
    wa
    #
    @16
    @37
    @1
    @31
    @11
    @28
    wcel
    #
    @38
    wa
    #
    @39
    @1
    cF
    wfun
    @31
    @41
    wb
    @0
    cC
    cF
    ffun
    @11
    @30
    cF
    funbrfv2b
    syl
    @1
    @40
    @22
    @38
    @1
    @40
    @23
    @22
    @1
    @28
    @0
    @11
    @35
    eleq2d
    @9
    @10
    cA
    cB
    opelxp
    syl6bb
    anbi1d
    bitrd
    @16
    @37
    @16
    @37
    wa
    #
    @39
    @16
    @37
    ibar
    @42
    @22
    @36
    wa
    @39
    @16
    @20
    @36
    anass
    @36
    @38
    @22
    @30
    @12
    eqcom
    anbi2i
    bitr3i
    syl6rbb
    sylan9bb
    opabbidv
    vy
    vz
    cB
    @12
    df-mpt
    syl6eqr
    mpteq2dva
    adantr
    eqtrd
    syl5eq
    feq1d
    sylan2
    3adant3
    mpbird
end
