include "wcel.mm"
include "wss.mm"
include "csubmnd.mm"
include "cfv.mm"
include "w3a.mm"
include "cima.mm"
include "cword.mm"
include "wa.mm"
include "cv.mm"
include "ccom.mm"
include "cgsu.mm"
include "co.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl2.mm"
include "sswrd.mm"
include "syl.mm"
include "simprr.mm"
include "sseldd.mm"
include "frmdgsum.mm"
include "syl2anc.mm"
include "simpl3.mm"
include "cres.mm"
include "crn.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "wf.mm"
include "wrdf.mm"
include "ad2antll.mm"
include "frn.mm"
include "cores.mm"
include "wfn.mm"
include "vrmdf.mm"
include "3ad2ant1.mm"
include "ffn.mm"
include "adantr.mm"
include "fnssres.mm"
include "df-ima.mm"
include "simprl.mm"
include "syl5eqssr.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "wrdco.mm"
include "eqeltrrd.mm"
include "gsumwsubmcl.mm"
include "expr.mm"
include "ssrdv.mm"
include "ex.mm"
include "wi.mm"
include "wral.mm"
include "cs1.mm"
include "simp2.mm"
include "sselda.mm"
include "vrmdval.mm"
include "simpr.mm"
include "s1cld.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "wfun.mm"
include "cdm.mm"
include "wb.mm"
include "fnfun.mm"
include "fndm.mm"
include "sseqtr4d.mm"
include "funimass4.mm"
include "mpbird.mm"
include "sstr2.mm"
include "impbid.mm"

theorem frmdss2
  let cA: class A
  let cU: class U
  let cI: class I
  let cJ: class J
  let cM: class M
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cW: class W
  assume frmdmnd.m: |- M = ( freeMnd ` I )
  assume frmdgsum.u: |- U = ( varFMnd ` I )


  assert |- ( ( I e. V /\ J C_ I /\ A e. ( SubMnd ` M ) ) -> ( ( U " J ) C_ A <-> Word J C_ A ) )

  proof
    cI
    cV
    wcel
    #
    cJ
    cI
    wss
    #
    cA
    cM
    csubmnd
    cfv
    wcel
    #
    w3a
    #
    cU
    cJ
    cima
    #
    cA
    wss
    #
    cJ
    cword
    #
    cA
    wss
    #
    @3
    @5
    @7
    @3
    @5
    wa
    vx
    @6
    cA
    @3
    @5
    vx
    cv
    #
    @6
    wcel
    #
    @8
    cA
    wcel
    @3
    @5
    @9
    wa
    #
    wa
    #
    cM
    cU
    @8
    ccom
    #
    cgsu
    co
    #
    @8
    cA
    @11
    @0
    @8
    cI
    cword
    #
    wcel
    @13
    @8
    wceq
    @0
    @1
    @2
    @10
    simpl1
    @11
    @6
    @14
    @8
    @11
    @1
    @6
    @14
    wss
    @0
    @1
    @2
    @10
    simpl2
    #
    cJ
    cI
    sswrd
    syl
    @3
    @5
    @9
    simprr
    #
    sseldd
    cU
    cI
    cM
    cV
    @8
    frmdmnd.m
    frmdgsum.u
    frmdgsum
    syl2anc
    @11
    @2
    @12
    cA
    cword
    #
    wcel
    @13
    cA
    wcel
    @0
    @1
    @2
    @10
    simpl3
    @11
    cU
    cJ
    cres
    #
    @8
    ccom
    #
    @12
    @17
    @11
    @8
    crn
    cJ
    wss
    #
    @19
    @12
    wceq
    @11
    cc0
    @8
    chash
    cfv
    cfzo
    co
    #
    cJ
    @8
    wf
    #
    @20
    @9
    @22
    @3
    @5
    cJ
    @8
    wrdf
    ad2antll
    @21
    cJ
    @8
    frn
    syl
    cU
    @8
    cJ
    cores
    syl
    @11
    @9
    cJ
    cA
    @18
    wf
    #
    @19
    @17
    wcel
    @16
    @11
    @18
    cJ
    wfn
    #
    @18
    crn
    #
    cA
    wss
    @23
    @11
    cU
    cI
    wfn
    #
    @1
    @24
    @3
    @26
    @10
    @3
    cI
    @14
    cU
    wf
    #
    @26
    @0
    @1
    @27
    @2
    cU
    cI
    cV
    frmdgsum.u
    vrmdf
    3ad2ant1
    cI
    @14
    cU
    ffn
    syl
    #
    adantr
    @15
    cI
    cJ
    cU
    fnssres
    syl2anc
    @11
    @25
    @4
    cA
    cU
    cJ
    df-ima
    @3
    @5
    @9
    simprl
    syl5eqssr
    cJ
    cA
    @18
    df-f
    sylanbrc
    cJ
    cA
    @18
    @8
    wrdco
    syl2anc
    eqeltrrd
    cA
    cM
    @12
    gsumwsubmcl
    syl2anc
    eqeltrrd
    expr
    ssrdv
    ex
    @3
    @4
    @6
    wss
    #
    @7
    @5
    wi
    @3
    @29
    @8
    cU
    cfv
    #
    @6
    wcel
    #
    vx
    cJ
    wral
    #
    @3
    @31
    vx
    cJ
    @3
    @8
    cJ
    wcel
    #
    wa
    #
    @30
    @8
    cs1
    #
    @6
    @34
    @0
    @8
    cI
    wcel
    @30
    @35
    wceq
    @0
    @1
    @2
    @33
    simpl1
    @3
    cJ
    cI
    @8
    @0
    @1
    @2
    simp2
    #
    sselda
    @8
    cU
    cI
    cV
    frmdgsum.u
    vrmdval
    syl2anc
    @34
    @8
    cJ
    @3
    @33
    simpr
    s1cld
    eqeltrd
    ralrimiva
    @3
    cU
    wfun
    #
    cJ
    cU
    cdm
    #
    wss
    @29
    @32
    wb
    @3
    @26
    @37
    @28
    cI
    cU
    fnfun
    syl
    @3
    cJ
    cI
    @38
    @36
    @3
    @26
    @38
    cI
    wceq
    @28
    cI
    cU
    fndm
    syl
    sseqtr4d
    vx
    cJ
    @6
    cU
    funimass4
    syl2anc
    mpbird
    @4
    @6
    cA
    sstr2
    syl
    impbid
end
