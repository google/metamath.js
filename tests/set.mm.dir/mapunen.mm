include "wcel.mm"
include "w3a.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "cun.mm"
include "cmap.mm"
include "co.mm"
include "cxp.mm"
include "cv.mm"
include "cres.mm"
include "cop.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cvv.mm"
include "ovex.mm"
include "a1i.mm"
include "xpex.mm"
include "wf.mm"
include "wss.mm"
include "elmapi.mm"
include "ssun1.mm"
include "fssres.mm"
include "sylancl.mm"
include "ssun2.mm"
include "jca.mm"
include "opelxp.mm"
include "simpl3.mm"
include "simpl1.mm"
include "elmapd.mm"
include "simpl2.mm"
include "anbi12d.mm"
include "syl5bb.mm"
include "syl5ibr.mm"
include "xp1st.mm"
include "adantl.mm"
include "syl.mm"
include "xp2nd.mm"
include "simplr.mm"
include "fun2.mm"
include "syl21anc.mm"
include "ex.mm"
include "unexg.mm"
include "syl2anc.mm"
include "sylibrd.mm"
include "wb.mm"
include "1st2nd2.mm"
include "ad2antll.mm"
include "adantrl.mm"
include "res0.mm"
include "eqtr4i.mm"
include "reseq2d.mm"
include "3eqtr4a.mm"
include "fresaunres1.mm"
include "syl3anc.mm"
include "fresaunres2.mm"
include "opeq12d.mm"
include "eqtr4d.mm"
include "reseq1.mm"
include "eqeq2d.mm"
include "syl5ibrcom.mm"
include "wfn.mm"
include "ffn.mm"
include "fnresdm.mm"
include "3syl.mm"
include "ad2antrl.mm"
include "eqcomd.mm"
include "vex.mm"
include "resex.mm"
include "op1std.mm"
include "op2ndd.mm"
include "uneq12d.mm"
include "resundi.mm"
include "syl6eqr.mm"
include "impbid.mm"
include "en3d.mm"

theorem mapunen
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let cX: class X
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( A e. V /\ B e. W /\ C e. X ) /\ ( A i^i B ) = (/) ) -> ( C ^m ( A u. B ) ) ~~ ( ( C ^m A ) X. ( C ^m B ) ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    cC
    cX
    wcel
    #
    w3a
    #
    cA
    cB
    cin
    #
    c0
    wceq
    #
    wa
    #
    vx
    vy
    cC
    cA
    cB
    cun
    #
    cmap
    co
    #
    cC
    cA
    cmap
    co
    #
    cC
    cB
    cmap
    co
    #
    cxp
    #
    vx
    cv
    #
    cA
    cres
    #
    @12
    cB
    cres
    #
    cop
    #
    vy
    cv
    #
    c1st
    cfv
    #
    @16
    c2nd
    cfv
    #
    cun
    #
    @8
    cvv
    wcel
    @6
    cC
    @7
    cmap
    ovex
    a1i
    @11
    cvv
    wcel
    @6
    @9
    @10
    cC
    cA
    cmap
    ovex
    cC
    cB
    cmap
    ovex
    xpex
    a1i
    @12
    @8
    wcel
    #
    @15
    @11
    wcel
    #
    @6
    cA
    cC
    @13
    wf
    #
    cB
    cC
    @14
    wf
    #
    wa
    #
    @20
    @22
    @23
    @20
    @7
    cC
    @12
    wf
    #
    cA
    @7
    wss
    @22
    @12
    cC
    @7
    elmapi
    #
    cA
    cB
    ssun1
    @7
    cC
    cA
    @12
    fssres
    sylancl
    @20
    @25
    cB
    @7
    wss
    @23
    @26
    cB
    cA
    ssun2
    @7
    cC
    cB
    @12
    fssres
    sylancl
    jca
    @21
    @13
    @9
    wcel
    #
    @14
    @10
    wcel
    #
    wa
    @6
    @24
    @13
    @14
    @9
    @10
    opelxp
    @6
    @27
    @22
    @28
    @23
    @6
    cC
    cA
    @13
    cX
    cV
    @0
    @1
    @2
    @5
    simpl3
    #
    @0
    @1
    @2
    @5
    simpl1
    #
    elmapd
    @6
    cC
    cB
    @14
    cX
    cW
    @29
    @0
    @1
    @2
    @5
    simpl2
    #
    elmapd
    anbi12d
    syl5bb
    syl5ibr
    @6
    @16
    @11
    wcel
    #
    @7
    cC
    @19
    wf
    #
    @19
    @8
    wcel
    @6
    @32
    @33
    @6
    @32
    wa
    #
    cA
    cC
    @17
    wf
    #
    cB
    cC
    @18
    wf
    #
    @5
    @33
    @34
    @17
    @9
    wcel
    #
    @35
    @32
    @37
    @6
    @16
    @9
    @10
    xp1st
    adantl
    @17
    cC
    cA
    elmapi
    syl
    #
    @34
    @18
    @10
    wcel
    #
    @36
    @32
    @39
    @6
    @16
    @9
    @10
    xp2nd
    adantl
    @18
    cC
    cB
    elmapi
    syl
    #
    @3
    @5
    @32
    simplr
    cA
    cB
    cC
    @17
    @18
    fun2
    syl21anc
    ex
    @6
    cC
    @7
    @19
    cX
    cvv
    @29
    @6
    @0
    @1
    @7
    cvv
    wcel
    @30
    @31
    cA
    cB
    cV
    cW
    unexg
    syl2anc
    elmapd
    sylibrd
    @6
    @20
    @32
    wa
    #
    @12
    @19
    wceq
    #
    @16
    @15
    wceq
    #
    wb
    @6
    @41
    wa
    #
    @42
    @43
    @44
    @43
    @42
    @16
    @19
    cA
    cres
    #
    @19
    cB
    cres
    #
    cop
    #
    wceq
    @44
    @16
    @17
    @18
    cop
    #
    @47
    @32
    @16
    @48
    wceq
    @6
    @20
    @16
    @9
    @10
    1st2nd2
    ad2antll
    @44
    @45
    @17
    @46
    @18
    @44
    @35
    @36
    @17
    @4
    cres
    #
    @18
    @4
    cres
    #
    wceq
    #
    @45
    @17
    wceq
    @6
    @32
    @35
    @20
    @38
    adantrl
    #
    @6
    @32
    @36
    @20
    @40
    adantrl
    #
    @44
    @17
    c0
    cres
    #
    @18
    c0
    cres
    #
    @49
    @50
    @54
    c0
    @55
    @17
    res0
    @18
    res0
    eqtr4i
    @44
    @4
    c0
    @17
    @3
    @5
    @41
    simplr
    #
    reseq2d
    @44
    @4
    c0
    @18
    @56
    reseq2d
    3eqtr4a
    #
    cA
    cB
    cC
    @17
    @18
    fresaunres1
    syl3anc
    @44
    @35
    @36
    @51
    @46
    @18
    wceq
    @52
    @53
    @57
    cA
    cB
    cC
    @17
    @18
    fresaunres2
    syl3anc
    opeq12d
    eqtr4d
    @42
    @15
    @47
    @16
    @42
    @13
    @45
    @14
    @46
    @12
    @19
    cA
    reseq1
    @12
    @19
    cB
    reseq1
    opeq12d
    eqeq2d
    syl5ibrcom
    @44
    @42
    @43
    @12
    @12
    @7
    cres
    #
    wceq
    @44
    @58
    @12
    @20
    @58
    @12
    wceq
    #
    @6
    @32
    @20
    @25
    @12
    @7
    wfn
    @59
    @26
    @7
    cC
    @12
    ffn
    @7
    @12
    fnresdm
    3syl
    ad2antrl
    eqcomd
    @43
    @19
    @58
    @12
    @43
    @19
    @13
    @14
    cun
    @58
    @43
    @17
    @13
    @18
    @14
    @13
    @14
    @16
    @12
    cA
    vx
    vex
    #
    resex
    #
    @12
    cB
    @60
    resex
    #
    op1std
    @13
    @14
    @16
    @61
    @62
    op2ndd
    uneq12d
    @12
    cA
    cB
    resundi
    syl6eqr
    eqeq2d
    syl5ibrcom
    impbid
    ex
    en3d
end
