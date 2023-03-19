include "cn.mm"
include "cen.mm"
include "wbr.mm"
include "cr.mm"
include "wss.mm"
include "covol.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "ensym.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "bren.mm"
include "wa.mm"
include "cle.mm"
include "caddc.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cid.mm"
include "cof.mm"
include "co.mm"
include "c1.mm"
include "cseq.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cxp.mm"
include "cin.mm"
include "wf.mm"
include "cicc.mm"
include "cuni.mm"
include "cmpt.mm"
include "cop.mm"
include "wcel.mm"
include "simpll.mm"
include "f1of.mm"
include "adantl.mm"
include "ffvelrnda.mm"
include "sseldd.mm"
include "leidd.mm"
include "df-br.mm"
include "sylib.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "elind.mm"
include "df-ov.mm"
include "cvv.mm"
include "opex.mm"
include "fvi.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "mpteq2i.mm"
include "fmptd.mm"
include "cc.mm"
include "nnex.mm"
include "a1i.mm"
include "recnd.mm"
include "feqmptd.mm"
include "offval2.mm"
include "feq1d.mm"
include "mpbird.mm"
include "c1st.mm"
include "c2nd.mm"
include "wrex.mm"
include "wral.mm"
include "wfo.mm"
include "f1ofo.mm"
include "forn.mm"
include "syl.mm"
include "eleq2d.mm"
include "wfn.mm"
include "wb.mm"
include "f1ofn.mm"
include "fvelrnb.mm"
include "bitr3d.mm"
include "syl6eq.mm"
include "fveq1d.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "sylan9eq.mm"
include "fveq2d.mm"
include "fvex.mm"
include "op1st.mm"
include "eqbrtrd.mm"
include "op2nd.mm"
include "breqtrrd.mm"
include "jca.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "syl5ibcom.mm"
include "reximdva.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "ovolficc.mm"
include "syldan.mm"
include "ovollb2.mm"
include "csn.mm"
include "absf.mm"
include "subf.mm"
include "fco.mm"
include "mp2an.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fmptco.mm"
include "cme.mm"
include "cnmet.mm"
include "met0.mm"
include "sylancr.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "fconstmpt.mm"
include "seqeq3d.mm"
include "cz.mm"
include "1z.mm"
include "nnuz.mm"
include "ser0f.mm"
include "rneqd.mm"
include "c0.mm"
include "wne.mm"
include "1nn.mm"
include "ne0i.mm"
include "rnxp.mm"
include "mp2b.mm"
include "supeq1d.mm"
include "wor.mm"
include "xrltso.mm"
include "0xr.mm"
include "supsn.mm"
include "breqtrd.mm"
include "ovolge0.mm"
include "adantr.mm"
include "ovolcl.mm"
include "xrletri3.mm"
include "sylancl.mm"
include "mpbir2and.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "imp.mm"
include "sylan2.mm"

theorem ovolctb
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let vk: setvar k
  let cB: class B
  let wph: wff ph
  let cS: class S
  let cT: class T


  assert |- ( ( A C_ RR /\ A ~~ NN ) -> ( vol* ` A ) = 0 )

  proof
    cA
    cn
    cen
    wbr
    cA
    cr
    wss
    #
    cn
    cA
    cen
    wbr
    #
    cA
    covol
    cfv
    #
    cc0
    wceq
    #
    cA
    cn
    ensym
    @0
    @1
    @3
    @1
    cn
    cA
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    @0
    @3
    cn
    cA
    vf
    bren
    @0
    @5
    @3
    vf
    @0
    @5
    @3
    @0
    @5
    wa
    #
    @3
    @2
    cc0
    cle
    wbr
    #
    cc0
    @2
    cle
    wbr
    #
    @6
    @2
    caddc
    cabs
    cmin
    ccom
    #
    @4
    @4
    cid
    cof
    co
    #
    ccom
    #
    c1
    cseq
    #
    crn
    #
    cxr
    clt
    csup
    #
    cc0
    cle
    @6
    cn
    cle
    cr
    cr
    cxp
    #
    cin
    #
    @10
    wf
    #
    cA
    cicc
    @10
    ccom
    crn
    cuni
    wss
    #
    @2
    @14
    cle
    wbr
    @6
    @17
    cn
    @16
    vx
    cn
    vx
    cv
    #
    @4
    cfv
    #
    @20
    cid
    co
    #
    cmpt
    #
    wf
    @6
    vx
    cn
    @20
    @20
    cop
    #
    @16
    @22
    @6
    @19
    cn
    wcel
    #
    wa
    #
    cle
    @15
    @23
    @25
    @20
    @20
    cle
    wbr
    @23
    cle
    wcel
    @25
    @20
    @25
    cA
    cr
    @20
    @0
    @5
    @24
    simpll
    @6
    cn
    cA
    @19
    @4
    @5
    cn
    cA
    @4
    wf
    @0
    cn
    cA
    @4
    f1of
    adantl
    #
    ffvelrnda
    sseldd
    #
    leidd
    #
    @20
    @20
    cle
    df-br
    sylib
    @25
    @20
    cr
    wcel
    #
    @29
    @23
    @15
    wcel
    @27
    @27
    @20
    @20
    cr
    cr
    opelxpi
    syl2anc
    elind
    vx
    cn
    @21
    @23
    @21
    @23
    cid
    cfv
    #
    @23
    @20
    @20
    cid
    df-ov
    @23
    cvv
    wcel
    #
    @30
    @23
    wceq
    @20
    @20
    opex
    #
    @23
    cvv
    fvi
    ax-mp
    eqtri
    mpteq2i
    #
    fmptd
    @6
    cn
    @16
    @10
    @22
    @6
    vx
    cn
    @20
    @20
    cid
    @4
    @4
    cvv
    cc
    cc
    cn
    cvv
    wcel
    @6
    nnex
    a1i
    @25
    @20
    @27
    recnd
    #
    @34
    @6
    vx
    cn
    cA
    @4
    @26
    feqmptd
    #
    @35
    offval2
    #
    feq1d
    mpbird
    #
    @6
    @18
    @19
    @10
    cfv
    #
    c1st
    cfv
    #
    vy
    cv
    #
    cle
    wbr
    #
    @40
    @38
    c2nd
    cfv
    #
    cle
    wbr
    #
    wa
    #
    vx
    cn
    wrex
    #
    vy
    cA
    wral
    #
    @6
    @45
    vy
    cA
    @6
    @40
    cA
    wcel
    #
    @20
    @40
    wceq
    #
    vx
    cn
    wrex
    #
    @45
    @6
    @40
    @4
    crn
    #
    wcel
    #
    @47
    @49
    @6
    @50
    cA
    @40
    @6
    cn
    cA
    @4
    wfo
    #
    @50
    cA
    wceq
    @5
    @52
    @0
    cn
    cA
    @4
    f1ofo
    adantl
    cn
    cA
    @4
    forn
    syl
    eleq2d
    @6
    @4
    cn
    wfn
    #
    @51
    @49
    wb
    @5
    @53
    @0
    cn
    cA
    @4
    f1ofn
    adantl
    vx
    cn
    @40
    @4
    fvelrnb
    syl
    bitr3d
    @6
    @48
    @44
    vx
    cn
    @25
    @39
    @20
    cle
    wbr
    #
    @20
    @42
    cle
    wbr
    #
    wa
    @48
    @44
    @25
    @54
    @55
    @25
    @39
    @20
    @20
    cle
    @25
    @39
    @23
    c1st
    cfv
    @20
    @25
    @38
    @23
    c1st
    @6
    @24
    @38
    @19
    vx
    cn
    @23
    cmpt
    #
    cfv
    #
    @23
    @6
    @19
    @10
    @56
    @6
    @10
    @22
    @56
    @36
    @33
    syl6eq
    #
    fveq1d
    @24
    @31
    @57
    @23
    wceq
    @32
    vx
    cn
    @23
    cvv
    @56
    @56
    eqid
    fvmpt2
    mpan2
    sylan9eq
    #
    fveq2d
    @20
    @20
    @19
    @4
    fvex
    #
    @60
    op1st
    syl6eq
    @28
    eqbrtrd
    @25
    @20
    @20
    @42
    cle
    @28
    @25
    @42
    @23
    c2nd
    cfv
    @20
    @25
    @38
    @23
    c2nd
    @59
    fveq2d
    @20
    @20
    @60
    @60
    op2nd
    syl6eq
    breqtrrd
    jca
    @48
    @54
    @41
    @55
    @43
    @20
    @40
    @39
    cle
    breq2
    @20
    @40
    @42
    cle
    breq1
    anbi12d
    syl5ibcom
    reximdva
    sylbid
    ralrimiv
    @0
    @5
    @17
    @18
    @46
    wb
    @37
    vy
    cA
    vx
    @10
    ovolficc
    syldan
    mpbird
    cA
    @12
    @10
    @12
    eqid
    ovollb2
    syl2anc
    @6
    @14
    cc0
    csn
    #
    cxr
    clt
    csup
    #
    cc0
    @6
    cxr
    @13
    @61
    clt
    @6
    @13
    cn
    @61
    cxp
    #
    crn
    #
    @61
    @6
    @12
    @63
    @6
    @12
    caddc
    @63
    c1
    cseq
    #
    @63
    @6
    @11
    @63
    caddc
    c1
    @6
    @11
    vx
    cn
    cc0
    cmpt
    #
    @63
    @6
    @11
    vx
    cn
    @20
    @20
    @9
    co
    #
    cmpt
    @66
    @6
    vx
    vy
    cn
    cc
    cc
    cxp
    #
    @23
    @40
    @9
    cfv
    #
    @67
    @10
    @9
    @25
    @20
    cc
    wcel
    #
    @70
    @23
    @68
    wcel
    @34
    @34
    @20
    @20
    cc
    cc
    opelxpi
    syl2anc
    @58
    @6
    vy
    @68
    cr
    @9
    @68
    cr
    @9
    wf
    #
    @6
    cc
    cr
    cabs
    wf
    @68
    cc
    cmin
    wf
    @71
    absf
    subf
    @68
    cc
    cr
    cabs
    cmin
    fco
    mp2an
    a1i
    feqmptd
    @40
    @23
    wceq
    @69
    @23
    @9
    cfv
    @67
    @40
    @23
    @9
    fveq2
    @20
    @20
    @9
    df-ov
    syl6eqr
    fmptco
    @6
    vx
    cn
    @67
    cc0
    @25
    @9
    cc
    cme
    cfv
    wcel
    @70
    @67
    cc0
    wceq
    cnmet
    @34
    @20
    @9
    cc
    met0
    sylancr
    mpteq2dva
    eqtrd
    vx
    cn
    cc0
    fconstmpt
    syl6eqr
    seqeq3d
    c1
    cz
    wcel
    @65
    @63
    wceq
    1z
    c1
    cn
    nnuz
    ser0f
    ax-mp
    syl6eq
    rneqd
    c1
    cn
    wcel
    cn
    c0
    wne
    @64
    @61
    wceq
    1nn
    cn
    c1
    ne0i
    cn
    @61
    rnxp
    mp2b
    syl6eq
    supeq1d
    cxr
    clt
    wor
    cc0
    cxr
    wcel
    #
    @62
    cc0
    wceq
    xrltso
    0xr
    cxr
    cc0
    clt
    supsn
    mp2an
    syl6eq
    breqtrd
    @0
    @8
    @5
    cA
    ovolge0
    adantr
    @6
    @2
    cxr
    wcel
    #
    @72
    @3
    @7
    @8
    wa
    wb
    @0
    @73
    @5
    cA
    ovolcl
    adantr
    0xr
    @2
    cc0
    xrletri3
    sylancl
    mpbir2and
    ex
    exlimdv
    syl5bi
    imp
    sylan2
end
