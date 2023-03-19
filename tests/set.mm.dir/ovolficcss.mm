include "cn.mm"
include "cle.mm"
include "cr.mm"
include "cxp.mm"
include "cin.mm"
include "wf.mm"
include "cicc.mm"
include "ccom.mm"
include "crn.mm"
include "cpw.mm"
include "wss.mm"
include "cuni.mm"
include "cima.mm"
include "rnco2.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "c1st.mm"
include "c2nd.mm"
include "co.mm"
include "cop.mm"
include "wceq.mm"
include "inss2.mm"
include "ffvelrn.mm"
include "sseldi.mm"
include "1st2nd2.mm"
include "syl.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "xp1st.mm"
include "xp2nd.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "eqsstrd.mm"
include "reex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "ralrimiva.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "ralrn.mm"
include "mpbird.mm"
include "wfun.mm"
include "cdm.mm"
include "cxr.mm"
include "iccf.mm"
include "ffun.mm"
include "ax-mp.mm"
include "frn.mm"
include "rexpssxrxp.mm"
include "sstri.mm"
include "fdmi.mm"
include "sseqtr4i.mm"
include "syl6ss.mm"
include "funimass4.mm"
include "sylancr.mm"
include "syl5eqss.mm"
include "sspwuni.mm"
include "sylib.mm"

theorem ovolficcss
  let cF: class F
  let vn: setvar n
  let vz: setvar z
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( F : NN --> ( <_ i^i ( RR X. RR ) ) -> U. ran ( [,] o. F ) C_ RR )

  proof
    cn
    cle
    cr
    cr
    cxp
    #
    cin
    #
    cF
    wf
    #
    cicc
    cF
    ccom
    crn
    #
    cr
    cpw
    #
    wss
    @3
    cuni
    cr
    wss
    @2
    @3
    cicc
    cF
    crn
    #
    cima
    #
    @4
    cicc
    cF
    rnco2
    @2
    @6
    @4
    wss
    #
    vx
    cv
    #
    cicc
    cfv
    #
    @4
    wcel
    #
    vx
    @5
    wral
    #
    @2
    @11
    vy
    cv
    #
    cF
    cfv
    #
    cicc
    cfv
    #
    @4
    wcel
    #
    vy
    cn
    wral
    #
    @2
    @15
    vy
    cn
    @2
    @12
    cn
    wcel
    wa
    #
    @14
    cr
    wss
    @15
    @17
    @14
    @13
    c1st
    cfv
    #
    @13
    c2nd
    cfv
    #
    cicc
    co
    #
    cr
    @17
    @14
    @18
    @19
    cop
    #
    cicc
    cfv
    @20
    @17
    @13
    @21
    cicc
    @17
    @13
    @0
    wcel
    #
    @13
    @21
    wceq
    @17
    @1
    @0
    @13
    cle
    @0
    inss2
    #
    cn
    @1
    @12
    cF
    ffvelrn
    sseldi
    #
    @13
    cr
    cr
    1st2nd2
    syl
    fveq2d
    @18
    @19
    cicc
    df-ov
    syl6eqr
    @17
    @18
    cr
    wcel
    #
    @19
    cr
    wcel
    #
    @20
    cr
    wss
    @17
    @22
    @25
    @24
    @13
    cr
    cr
    xp1st
    syl
    @17
    @22
    @26
    @24
    @13
    cr
    cr
    xp2nd
    syl
    @18
    @19
    iccssre
    syl2anc
    eqsstrd
    @14
    cr
    reex
    elpw2
    sylibr
    ralrimiva
    @2
    cF
    cn
    wfn
    @11
    @16
    wb
    cn
    @1
    cF
    ffn
    @10
    @15
    vx
    vy
    cn
    cF
    @8
    @13
    wceq
    @9
    @14
    @4
    @8
    @13
    cicc
    fveq2
    eleq1d
    ralrn
    syl
    mpbird
    @2
    cicc
    wfun
    #
    @5
    cicc
    cdm
    #
    wss
    @7
    @11
    wb
    cxr
    cxr
    cxp
    #
    cxr
    cpw
    #
    cicc
    wf
    @27
    iccf
    @29
    @30
    cicc
    ffun
    ax-mp
    @2
    @5
    @1
    @28
    cn
    @1
    cF
    frn
    @1
    @29
    @28
    @1
    @0
    @29
    @23
    rexpssxrxp
    sstri
    @29
    @30
    cicc
    iccf
    fdmi
    sseqtr4i
    syl6ss
    vx
    @5
    @4
    cicc
    funimass4
    sylancr
    mpbird
    syl5eqss
    @3
    cr
    sspwuni
    sylib
end
