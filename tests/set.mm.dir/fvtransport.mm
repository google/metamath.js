include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "cop.mm"
include "ctransport.mm"
include "co.mm"
include "cv.mm"
include "cbtwn.mm"
include "wbr.mm"
include "ccgr.mm"
include "crio.mm"
include "df-ov.mm"
include "cxp.mm"
include "c1st.mm"
include "c2nd.mm"
include "wceq.mm"
include "wrex.mm"
include "opelxpi.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "op1stg.mm"
include "op2ndg.mm"
include "3netr4d.mm"
include "3jca.mm"
include "opeq1d.mm"
include "breq12d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "riotabidv.mm"
include "eqcomd.mm"
include "jca.mm"
include "fveq2.mm"
include "sqxpeqd.mm"
include "eleq2d.mm"
include "3anbi12d.mm"
include "riotaeqdv.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "sylan2.mm"
include "coprab.mm"
include "df-br.mm"
include "df-transport.mm"
include "eleq2i.mm"
include "cvv.mm"
include "wb.mm"
include "opex.mm"
include "riotaex.mm"
include "eleq1.mm"
include "3anbi1d.mm"
include "breq2.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "neeq12d.mm"
include "3anbi23d.mm"
include "eqeq1.mm"
include "eloprabg.mm"
include "mp3an.mm"
include "3bitri.mm"
include "wfun.mm"
include "wi.mm"
include "funtransport.mm"
include "funbrfv.mm"
include "ax-mp.mm"
include "sylbir.mm"
include "syl.mm"
include "syl5eq.mm"

theorem fvtransport
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N
  let vr: setvar r
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vx: setvar x

  disjoint N r
  disjoint A r
  disjoint B r
  disjoint C r
  disjoint D r
  disjoint N n
  disjoint N p
  disjoint N q
  disjoint N x
  disjoint n p
  disjoint n q
  disjoint n r
  disjoint n x
  disjoint p q
  disjoint p r
  disjoint p x
  disjoint q r
  disjoint q x
  disjoint r x
  disjoint A n
  disjoint A p
  disjoint A q
  disjoint A x
  disjoint B n
  disjoint B p
  disjoint B q
  disjoint B x
  disjoint C n
  disjoint C p
  disjoint C q
  disjoint C x
  disjoint D n
  disjoint D p
  disjoint D q
  disjoint D x
  assert |- ( ( N e. NN /\ ( ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) /\ C =/= D ) ) -> ( <. A , B >. TransportTo <. C , D >. ) = ( iota_ r e. ( EE ` N ) ( D Btwn <. C , r >. /\ <. D , r >. Cgr <. A , B >. ) ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    cB
    @1
    wcel
    wa
    #
    cC
    @1
    wcel
    cD
    @1
    wcel
    wa
    #
    cC
    cD
    wne
    #
    w3a
    #
    wa
    #
    cA
    cB
    cop
    #
    cC
    cD
    cop
    #
    ctransport
    co
    @7
    @8
    cop
    #
    ctransport
    cfv
    #
    cD
    cC
    vr
    cv
    #
    cop
    #
    cbtwn
    wbr
    #
    cD
    @11
    cop
    #
    @7
    ccgr
    wbr
    #
    wa
    #
    vr
    @1
    crio
    #
    @7
    @8
    ctransport
    df-ov
    @6
    @7
    vn
    cv
    #
    cee
    cfv
    #
    @19
    cxp
    #
    wcel
    #
    @8
    @20
    wcel
    #
    @8
    c1st
    cfv
    #
    @8
    c2nd
    cfv
    #
    wne
    #
    w3a
    #
    @17
    @24
    @23
    @11
    cop
    #
    cbtwn
    wbr
    #
    @24
    @11
    cop
    #
    @7
    ccgr
    wbr
    #
    wa
    #
    vr
    @19
    crio
    #
    wceq
    #
    wa
    #
    vn
    cn
    wrex
    #
    @10
    @17
    wceq
    #
    @5
    @0
    @7
    @1
    @1
    cxp
    #
    wcel
    #
    @8
    @37
    wcel
    #
    @25
    w3a
    #
    @17
    @31
    vr
    @1
    crio
    #
    wceq
    #
    wa
    #
    @35
    @5
    @40
    @42
    @5
    @38
    @39
    @25
    @2
    @3
    @38
    @4
    cA
    cB
    @1
    @1
    opelxpi
    3ad2ant1
    @3
    @2
    @39
    @4
    cC
    cD
    @1
    @1
    opelxpi
    3ad2ant2
    @5
    cC
    cD
    @23
    @24
    @2
    @3
    @4
    simp3
    @3
    @2
    @23
    cC
    wceq
    @4
    cC
    cD
    @1
    @1
    op1stg
    3ad2ant2
    #
    @3
    @2
    @24
    cD
    wceq
    @4
    cC
    cD
    @1
    @1
    op2ndg
    3ad2ant2
    #
    3netr4d
    3jca
    @5
    @41
    @17
    @5
    @31
    @16
    vr
    @1
    @5
    @28
    @13
    @30
    @15
    @5
    @24
    cD
    @27
    @12
    cbtwn
    @45
    @5
    @23
    cC
    @11
    @44
    opeq1d
    breq12d
    @5
    @29
    @14
    @7
    ccgr
    @5
    @24
    cD
    @11
    @45
    opeq1d
    breq1d
    anbi12d
    riotabidv
    eqcomd
    jca
    @34
    @43
    vn
    cN
    cn
    @18
    cN
    wceq
    #
    @26
    @40
    @33
    @42
    @46
    @21
    @38
    @22
    @39
    @25
    @46
    @20
    @37
    @7
    @46
    @19
    @1
    @18
    cN
    cee
    fveq2
    #
    sqxpeqd
    #
    eleq2d
    @46
    @20
    @37
    @8
    @48
    eleq2d
    3anbi12d
    @46
    @32
    @41
    @17
    @46
    @31
    vr
    @19
    @1
    @47
    riotaeqdv
    eqeq2d
    anbi12d
    rspcev
    sylan2
    @35
    @9
    @17
    ctransport
    wbr
    #
    @36
    @49
    @9
    @17
    cop
    #
    ctransport
    wcel
    @50
    vp
    cv
    #
    @20
    wcel
    #
    vq
    cv
    #
    @20
    wcel
    #
    @53
    c1st
    cfv
    #
    @53
    c2nd
    cfv
    #
    wne
    #
    w3a
    #
    vx
    cv
    #
    @56
    @55
    @11
    cop
    #
    cbtwn
    wbr
    #
    @56
    @11
    cop
    #
    @51
    ccgr
    wbr
    #
    wa
    #
    vr
    @19
    crio
    #
    wceq
    #
    wa
    #
    vn
    cn
    wrex
    #
    vp
    vq
    vx
    coprab
    #
    wcel
    #
    @35
    @9
    @17
    ctransport
    df-br
    ctransport
    @69
    @50
    vx
    vn
    vr
    vq
    vp
    df-transport
    eleq2i
    @7
    cvv
    wcel
    @8
    cvv
    wcel
    @17
    cvv
    wcel
    @70
    @35
    wb
    cA
    cB
    opex
    cC
    cD
    opex
    @16
    vr
    @1
    riotaex
    @68
    @21
    @54
    @57
    w3a
    #
    @59
    @61
    @62
    @7
    ccgr
    wbr
    #
    wa
    #
    vr
    @19
    crio
    #
    wceq
    #
    wa
    #
    vn
    cn
    wrex
    @26
    @59
    @32
    wceq
    #
    wa
    #
    vn
    cn
    wrex
    @35
    vp
    vq
    vx
    @7
    @8
    @17
    cvv
    cvv
    cvv
    @51
    @7
    wceq
    #
    @67
    @76
    vn
    cn
    @79
    @58
    @71
    @66
    @75
    @79
    @52
    @21
    @54
    @57
    @51
    @7
    @20
    eleq1
    3anbi1d
    @79
    @65
    @74
    @59
    @79
    @64
    @73
    vr
    @19
    @79
    @63
    @72
    @61
    @51
    @7
    @62
    ccgr
    breq2
    anbi2d
    riotabidv
    eqeq2d
    anbi12d
    rexbidv
    @53
    @8
    wceq
    #
    @76
    @78
    vn
    cn
    @80
    @71
    @26
    @75
    @77
    @80
    @54
    @22
    @57
    @25
    @21
    @53
    @8
    @20
    eleq1
    @80
    @55
    @23
    @56
    @24
    @53
    @8
    c1st
    fveq2
    #
    @53
    @8
    c2nd
    fveq2
    #
    neeq12d
    3anbi23d
    @80
    @74
    @32
    @59
    @80
    @73
    @31
    vr
    @19
    @80
    @61
    @28
    @72
    @30
    @80
    @56
    @24
    @60
    @27
    cbtwn
    @82
    @80
    @55
    @23
    @11
    @81
    opeq1d
    breq12d
    @80
    @62
    @29
    @7
    ccgr
    @80
    @56
    @24
    @11
    @82
    opeq1d
    breq1d
    anbi12d
    riotabidv
    eqeq2d
    anbi12d
    rexbidv
    @59
    @17
    wceq
    #
    @78
    @34
    vn
    cn
    @83
    @77
    @33
    @26
    @59
    @17
    @32
    eqeq1
    anbi2d
    rexbidv
    eloprabg
    mp3an
    3bitri
    ctransport
    wfun
    @49
    @36
    wi
    funtransport
    @9
    @17
    ctransport
    funbrfv
    ax-mp
    sylbir
    syl
    syl5eq
end
