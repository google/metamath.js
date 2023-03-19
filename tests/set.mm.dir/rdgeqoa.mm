include "com.mm"
include "wcel.mm"
include "con0.mm"
include "w3a.mm"
include "crdg.mm"
include "cfv.mm"
include "wceq.mm"
include "coa.mm"
include "co.mm"
include "wi.mm"
include "simp3.mm"
include "cv.mm"
include "eleq1.mm"
include "3anbi3d.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "imbi12d.mm"
include "c0.mm"
include "wsbc.mm"
include "peano1.mm"
include "wal.mm"
include "wa.mm"
include "oa0.mm"
include "eqcomd.mm"
include "eqeqan12d.mm"
include "biimpd.mm"
include "biantru.mm"
include "anbi2i.mm"
include "3anass.mm"
include "bitr4i.mm"
include "syl6bbr.mm"
include "mpbiri.mm"
include "ax-gen.mm"
include "sbc6g.mm"
include "ax-mp.mm"
include "csuc.mm"
include "peano2b.mm"
include "3anbi3i.mm"
include "imbi1i.mm"
include "nnon.mm"
include "oacl.mm"
include "anim12i.mm"
include "3impdir.mm"
include "rdgsuc.mm"
include "fveq2.mm"
include "sylan9eqr.mm"
include "adantrr.mm"
include "ad2antll.mm"
include "eqtr4d.mm"
include "sylan2.mm"
include "ancoms.mm"
include "syl3anl3.mm"
include "onasuc.mm"
include "3adant2.mm"
include "adantr.mm"
include "3adant1.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "imim2d.mm"
include "sylbir.mm"
include "a2i.mm"
include "sylbi.mm"
include "sbcimg.mm"
include "sbc3an.mm"
include "sbcg.mm"
include "wb.mm"
include "sbcel1v.mm"
include "a1i.mm"
include "3anbi123d.mm"
include "syl5bb.mm"
include "csb.mm"
include "sbceqg.mm"
include "csbfv12.mm"
include "csbconstg.mm"
include "csbov123.mm"
include "csbvarg.mm"
include "oveq123d.mm"
include "syl5eq.mm"
include "fveq12d.mm"
include "bitrd.mm"
include "syl5ibr.mm"
include "findes.mm"
include "vtoclga.mm"
include "mpcom.mm"

theorem rdgeqoa
  let cA: class A
  let cB: class B
  let cF: class F
  let cM: class M
  let cN: class N
  let cX: class X
  let vx: setvar x


  assert |- ( ( N e. On /\ M e. On /\ X e. _om ) -> ( ( rec ( F , A ) ` N ) = ( rec ( F , B ) ` M ) -> ( rec ( F , A ) ` ( N +o X ) ) = ( rec ( F , B ) ` ( M +o X ) ) ) )

  proof
    cX
    com
    wcel
    #
    cN
    con0
    wcel
    #
    cM
    con0
    wcel
    #
    @0
    w3a
    #
    cN
    cF
    cA
    crdg
    #
    cfv
    #
    cM
    cF
    cB
    crdg
    #
    cfv
    #
    wceq
    #
    cN
    cX
    coa
    co
    #
    @4
    cfv
    #
    cM
    cX
    coa
    co
    #
    @6
    cfv
    #
    wceq
    #
    wi
    #
    @1
    @2
    @0
    simp3
    @1
    @2
    vx
    cv
    #
    com
    wcel
    #
    w3a
    #
    @8
    cN
    @15
    coa
    co
    #
    @4
    cfv
    #
    cM
    @15
    coa
    co
    #
    @6
    cfv
    #
    wceq
    #
    wi
    #
    wi
    #
    @3
    @14
    wi
    vx
    cX
    com
    @15
    cX
    wceq
    #
    @17
    @3
    @23
    @14
    @25
    @16
    @0
    @1
    @2
    @15
    cX
    com
    eleq1
    3anbi3d
    @25
    @22
    @13
    @8
    @25
    @19
    @10
    @21
    @12
    @25
    @18
    @9
    @4
    @15
    cX
    cN
    coa
    oveq2
    fveq2d
    @25
    @20
    @11
    @6
    @15
    cX
    cM
    coa
    oveq2
    fveq2d
    eqeq12d
    imbi2d
    imbi12d
    @24
    vx
    c0
    com
    wcel
    #
    @24
    vx
    c0
    wsbc
    #
    peano1
    @26
    @27
    @15
    c0
    wceq
    #
    @24
    wi
    #
    vx
    wal
    @29
    vx
    @28
    @24
    @1
    @2
    wa
    #
    @8
    cN
    c0
    coa
    co
    #
    @4
    cfv
    #
    cM
    c0
    coa
    co
    #
    @6
    cfv
    #
    wceq
    #
    wi
    #
    wi
    @30
    @8
    @35
    @1
    @2
    @5
    @32
    @7
    @34
    @1
    @32
    @5
    @1
    @31
    cN
    @4
    cN
    oa0
    fveq2d
    eqcomd
    @2
    @34
    @7
    @2
    @33
    cM
    @6
    cM
    oa0
    fveq2d
    eqcomd
    eqeqan12d
    biimpd
    @28
    @17
    @30
    @23
    @36
    @28
    @17
    @1
    @2
    @26
    w3a
    #
    @30
    @28
    @16
    @26
    @1
    @2
    @15
    c0
    com
    eleq1
    3anbi3d
    @30
    @1
    @2
    @26
    wa
    #
    wa
    @37
    @2
    @38
    @1
    @26
    @2
    peano1
    biantru
    anbi2i
    @1
    @2
    @26
    3anass
    bitr4i
    syl6bbr
    @28
    @22
    @35
    @8
    @28
    @19
    @32
    @21
    @34
    @28
    @18
    @31
    @4
    @15
    c0
    cN
    coa
    oveq2
    fveq2d
    @28
    @20
    @33
    @6
    @15
    c0
    cM
    coa
    oveq2
    fveq2d
    eqeq12d
    imbi2d
    imbi12d
    mpbiri
    ax-gen
    @24
    vx
    c0
    com
    sbc6g
    mpbiri
    ax-mp
    @16
    @15
    csuc
    #
    com
    wcel
    #
    @24
    @24
    vx
    @39
    wsbc
    #
    wi
    @15
    peano2b
    #
    @24
    @41
    @40
    @1
    @2
    @40
    w3a
    #
    @8
    cN
    @39
    coa
    co
    #
    @4
    cfv
    #
    cM
    @39
    coa
    co
    #
    @6
    cfv
    #
    wceq
    #
    wi
    #
    wi
    #
    @24
    @43
    @23
    wi
    @50
    @17
    @43
    @23
    @16
    @40
    @1
    @2
    @42
    3anbi3i
    #
    imbi1i
    @43
    @23
    @49
    @43
    @17
    @23
    @49
    wi
    @51
    @17
    @22
    @48
    @8
    @17
    @22
    @48
    @17
    @22
    wa
    @18
    csuc
    #
    @4
    cfv
    #
    @20
    csuc
    #
    @6
    cfv
    #
    @45
    @47
    @16
    @1
    @2
    @15
    con0
    wcel
    #
    @22
    @53
    @55
    wceq
    #
    @15
    nnon
    @22
    @1
    @2
    @56
    w3a
    #
    @57
    @58
    @22
    @18
    con0
    wcel
    #
    @20
    con0
    wcel
    #
    wa
    #
    @57
    @1
    @56
    @2
    @61
    @1
    @56
    wa
    @59
    @2
    @56
    wa
    @60
    cN
    @15
    oacl
    cM
    @15
    oacl
    anim12i
    3impdir
    @22
    @61
    wa
    @53
    @21
    cF
    cfv
    #
    @55
    @22
    @59
    @53
    @62
    wceq
    @60
    @59
    @22
    @53
    @19
    cF
    cfv
    @62
    cA
    @18
    cF
    rdgsuc
    @19
    @21
    cF
    fveq2
    sylan9eqr
    adantrr
    @60
    @55
    @62
    wceq
    @22
    @59
    cB
    @20
    cF
    rdgsuc
    ad2antll
    eqtr4d
    sylan2
    ancoms
    syl3anl3
    @17
    @45
    @53
    wceq
    #
    @22
    @1
    @16
    @63
    @2
    @1
    @16
    wa
    @44
    @52
    @4
    cN
    @15
    onasuc
    fveq2d
    3adant2
    adantr
    @17
    @47
    @55
    wceq
    #
    @22
    @2
    @16
    @64
    @1
    @2
    @16
    wa
    @46
    @54
    @6
    cM
    @15
    onasuc
    fveq2d
    3adant1
    adantr
    3eqtr4d
    ex
    imim2d
    sylbir
    a2i
    sylbi
    @40
    @41
    @17
    vx
    @39
    wsbc
    #
    @23
    vx
    @39
    wsbc
    #
    wi
    @50
    @17
    @23
    vx
    @39
    com
    sbcimg
    @40
    @65
    @43
    @66
    @49
    @65
    @1
    vx
    @39
    wsbc
    #
    @2
    vx
    @39
    wsbc
    #
    @16
    vx
    @39
    wsbc
    #
    w3a
    @40
    @43
    @1
    @2
    @16
    vx
    @39
    sbc3an
    @40
    @67
    @1
    @68
    @2
    @69
    @40
    @1
    vx
    @39
    com
    sbcg
    @2
    vx
    @39
    com
    sbcg
    @69
    @40
    wb
    @40
    vx
    @39
    com
    sbcel1v
    a1i
    3anbi123d
    syl5bb
    @40
    @66
    @8
    vx
    @39
    wsbc
    #
    @22
    vx
    @39
    wsbc
    #
    wi
    @49
    @8
    @22
    vx
    @39
    com
    sbcimg
    @40
    @70
    @8
    @71
    @48
    @8
    vx
    @39
    com
    sbcg
    @40
    @71
    vx
    @39
    @19
    csb
    #
    vx
    @39
    @21
    csb
    #
    wceq
    @48
    vx
    @39
    @19
    @21
    com
    sbceqg
    @40
    @72
    @45
    @73
    @47
    @40
    @72
    vx
    @39
    @18
    csb
    #
    vx
    @39
    @4
    csb
    #
    cfv
    @45
    vx
    @39
    @18
    @4
    csbfv12
    @40
    @74
    @44
    @75
    @4
    vx
    @39
    @4
    com
    csbconstg
    @40
    @74
    vx
    @39
    cN
    csb
    #
    vx
    @39
    @15
    csb
    #
    vx
    @39
    coa
    csb
    #
    co
    @44
    vx
    @39
    cN
    @15
    coa
    csbov123
    @40
    @76
    cN
    @77
    @39
    @78
    coa
    vx
    @39
    coa
    com
    csbconstg
    #
    vx
    @39
    cN
    com
    csbconstg
    vx
    @39
    com
    csbvarg
    #
    oveq123d
    syl5eq
    fveq12d
    syl5eq
    @40
    @73
    vx
    @39
    @20
    csb
    #
    vx
    @39
    @6
    csb
    #
    cfv
    @47
    vx
    @39
    @20
    @6
    csbfv12
    @40
    @81
    @46
    @82
    @6
    vx
    @39
    @6
    com
    csbconstg
    @40
    @81
    vx
    @39
    cM
    csb
    #
    @77
    @78
    co
    @46
    vx
    @39
    cM
    @15
    coa
    csbov123
    @40
    @83
    cM
    @77
    @39
    @78
    coa
    @79
    vx
    @39
    cM
    com
    csbconstg
    @80
    oveq123d
    syl5eq
    fveq12d
    syl5eq
    eqeq12d
    bitrd
    imbi12d
    bitrd
    imbi12d
    bitrd
    syl5ibr
    sylbi
    findes
    vtoclga
    mpcom
end
