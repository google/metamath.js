include "cstr.mm"
include "wbr.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "c1st.mm"
include "cfv.mm"
include "cle.mm"
include "cif.mm"
include "c2nd.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "csts.mm"
include "co.mm"
include "cxp.mm"
include "cin.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wfun.mm"
include "cdm.mm"
include "cfz.mm"
include "wss.mm"
include "wi.mm"
include "isstruct2.mm"
include "elin.mm"
include "elxp6.mm"
include "wb.mm"
include "eleq1.mm"
include "adantr.mm"
include "simp3.mm"
include "simp1l.mm"
include "ifcld.mm"
include "nnred.mm"
include "simp1r.mm"
include "cr.mm"
include "nnre.mm"
include "anim12i.mm"
include "3adant2.mm"
include "ancomd.mm"
include "min1.mm"
include "syl.mm"
include "adantl.mm"
include "max1.mm"
include "letrd.mm"
include "df-br.mm"
include "sylib.mm"
include "opelxpd.mm"
include "elind.mm"
include "3exp.mm"
include "sylbid.mm"
include "sylbi.mm"
include "impcom.mm"
include "3ad2ant1.mm"
include "imp.mm"
include "cvv.mm"
include "structex.mm"
include "structn0fun.mm"
include "jca.mm"
include "simp2.mm"
include "setsfun0.mm"
include "syl12anc.mm"
include "cun.mm"
include "setsdm.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "sseq2d.mm"
include "df-3an.mm"
include "cz.mm"
include "nnz.mm"
include "3anim123i.mm"
include "ssfzunsnext.mm"
include "syl6sseq.mm"
include "sylan2.mm"
include "ex.mm"
include "syl5bir.mm"
include "expd.mm"
include "com12.mm"
include "eqsstrd.mm"
include "syl3anbrc.mm"
include "breq2.mm"
include "mpbird.mm"

theorem setsstruct2
  let cE: class E
  let cG: class G
  let cI: class I
  let cV: class V
  let cX: class X
  let cY: class Y


  assert |- ( ( ( G Struct X /\ E e. V /\ I e. NN ) /\ Y = <. if ( I <_ ( 1st ` X ) , I , ( 1st ` X ) ) , if ( I <_ ( 2nd ` X ) , ( 2nd ` X ) , I ) >. ) -> ( G sSet <. I , E >. ) Struct Y )

  proof
    cG
    cX
    cstr
    wbr
    #
    cE
    cV
    wcel
    #
    cI
    cn
    wcel
    #
    w3a
    #
    cY
    cI
    cX
    c1st
    cfv
    #
    cle
    wbr
    #
    cI
    @4
    cif
    #
    cI
    cX
    c2nd
    cfv
    #
    cle
    wbr
    #
    @7
    cI
    cif
    #
    cop
    #
    wceq
    #
    wa
    cG
    cI
    cE
    cop
    csts
    co
    #
    cY
    cstr
    wbr
    #
    @12
    @10
    cstr
    wbr
    #
    @3
    @14
    @11
    @3
    @10
    cle
    cn
    cn
    cxp
    #
    cin
    #
    wcel
    #
    @12
    c0
    csn
    #
    cdif
    wfun
    #
    @12
    cdm
    #
    @10
    cfz
    cfv
    #
    wss
    @14
    @0
    @2
    @17
    @1
    @0
    @2
    @17
    @0
    cX
    @16
    wcel
    #
    cG
    @18
    cdif
    wfun
    #
    cG
    cdm
    #
    cX
    cfz
    cfv
    #
    wss
    #
    w3a
    #
    @2
    @17
    wi
    #
    cG
    cX
    isstruct2
    #
    @22
    @23
    @28
    @26
    @22
    cX
    cle
    wcel
    #
    cX
    @15
    wcel
    #
    wa
    #
    @28
    cX
    cle
    @15
    elin
    #
    @31
    @30
    @28
    @31
    cX
    @4
    @7
    cop
    #
    wceq
    #
    @4
    cn
    wcel
    #
    @7
    cn
    wcel
    #
    wa
    #
    wa
    #
    @30
    @28
    wi
    cX
    cn
    cn
    elxp6
    #
    @39
    @30
    @34
    cle
    wcel
    #
    @28
    @35
    @30
    @41
    wb
    @38
    cX
    @34
    cle
    eleq1
    adantr
    @38
    @41
    @28
    wi
    @35
    @38
    @41
    @2
    @17
    @38
    @41
    @2
    w3a
    #
    cle
    @15
    @10
    @42
    @6
    @9
    cle
    wbr
    @10
    cle
    wcel
    @42
    @6
    cI
    @9
    @42
    @6
    @42
    @5
    cI
    @4
    cn
    @38
    @41
    @2
    simp3
    #
    @36
    @37
    @41
    @2
    simp1l
    ifcld
    #
    nnred
    @42
    cI
    @43
    nnred
    @42
    @9
    @42
    @8
    @7
    cI
    cn
    @36
    @37
    @41
    @2
    simp1r
    @43
    ifcld
    #
    nnred
    @42
    cI
    cr
    wcel
    #
    @4
    cr
    wcel
    #
    wa
    @6
    cI
    cle
    wbr
    @42
    @47
    @46
    @38
    @2
    @47
    @46
    wa
    @41
    @38
    @47
    @2
    @46
    @36
    @47
    @37
    @4
    nnre
    adantr
    cI
    nnre
    #
    anim12i
    3adant2
    ancomd
    cI
    @4
    min1
    syl
    @42
    @46
    @7
    cr
    wcel
    #
    wa
    cI
    @9
    cle
    wbr
    @42
    @49
    @46
    @38
    @2
    @49
    @46
    wa
    @41
    @38
    @49
    @2
    @46
    @37
    @49
    @36
    @7
    nnre
    adantl
    @48
    anim12i
    3adant2
    ancomd
    cI
    @7
    max1
    syl
    letrd
    @6
    @9
    cle
    df-br
    sylib
    @42
    @6
    @9
    cn
    cn
    @44
    @45
    opelxpd
    elind
    3exp
    adantl
    sylbid
    sylbi
    impcom
    sylbi
    3ad2ant1
    sylbi
    imp
    3adant2
    @3
    cG
    cvv
    wcel
    #
    @23
    wa
    #
    @2
    @1
    @19
    @0
    @1
    @51
    @2
    @0
    @50
    @23
    cG
    cX
    structex
    #
    cG
    cX
    structn0fun
    jca
    3ad2ant1
    @0
    @1
    @2
    simp3
    @0
    @1
    @2
    simp2
    #
    cn
    cE
    cG
    cI
    cvv
    cV
    setsfun0
    syl12anc
    @3
    @20
    @24
    cI
    csn
    cun
    #
    @21
    @3
    @50
    @1
    wa
    @20
    @54
    wceq
    @3
    @50
    @1
    @0
    @1
    @50
    @2
    @52
    3ad2ant1
    @53
    jca
    cE
    cG
    cI
    cvv
    cV
    setsdm
    syl
    @0
    @2
    @54
    @21
    wss
    #
    @1
    @0
    @2
    @55
    @0
    @27
    @2
    @55
    wi
    #
    @29
    @22
    @26
    @56
    @23
    @22
    @26
    @56
    @22
    @32
    @26
    @56
    wi
    #
    @33
    @31
    @57
    @30
    @31
    @39
    @57
    @40
    @39
    @26
    @24
    @4
    @7
    cfz
    co
    #
    wss
    #
    @56
    @35
    @26
    @59
    wb
    @38
    @35
    @25
    @58
    @24
    @35
    @25
    @34
    cfz
    cfv
    @58
    cX
    @34
    cfz
    fveq2
    @4
    @7
    cfz
    df-ov
    syl6eqr
    sseq2d
    adantr
    @38
    @59
    @56
    wi
    @35
    @59
    @38
    @56
    @59
    @38
    @2
    @55
    @38
    @2
    wa
    @36
    @37
    @2
    w3a
    #
    @59
    @55
    @36
    @37
    @2
    df-3an
    @59
    @60
    @55
    @60
    @59
    @4
    cz
    wcel
    #
    @7
    cz
    wcel
    #
    cI
    cz
    wcel
    #
    w3a
    #
    @55
    @36
    @61
    @37
    @62
    @2
    @63
    @4
    nnz
    @7
    nnz
    cI
    nnz
    3anim123i
    @59
    @64
    wa
    @54
    @6
    @9
    cfz
    co
    @21
    @24
    cI
    @4
    @7
    ssfzunsnext
    @6
    @9
    cfz
    df-ov
    syl6sseq
    sylan2
    ex
    syl5bir
    expd
    com12
    adantl
    sylbid
    sylbi
    adantl
    sylbi
    imp
    3adant2
    sylbi
    imp
    3adant2
    eqsstrd
    @12
    @10
    isstruct2
    syl3anbrc
    adantr
    @11
    @13
    @14
    wb
    @3
    cY
    @10
    @12
    cstr
    breq2
    adantl
    mpbird
end
