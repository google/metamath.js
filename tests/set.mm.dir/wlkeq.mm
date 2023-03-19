include "cwlks.mm"
include "cfv.mm"
include "wcel.mm"
include "c1st.mm"
include "chash.mm"
include "wceq.mm"
include "w3a.mm"
include "c2nd.mm"
include "wa.mm"
include "cv.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wral.mm"
include "cfz.mm"
include "wb.mm"
include "cvv.mm"
include "cxp.mm"
include "cop.mm"
include "wlkop.mm"
include "1st2ndb.mm"
include "sylibr.mm"
include "xpopth.mm"
include "bicomd.mm"
include "syl2an.mm"
include "3adant3.mm"
include "ciedg.mm"
include "cdm.mm"
include "cword.mm"
include "cvtx.mm"
include "wf.mm"
include "c1.mm"
include "cmin.mm"
include "eqid.mm"
include "wlkelwrd.mm"
include "anim12i.mm"
include "eleq1.mm"
include "wbr.mm"
include "df-br.mm"
include "wlklenvm1.mm"
include "sylbir.mm"
include "syl6bi.mm"
include "mpcom.mm"
include "eqwrd.mm"
include "ad2ant2r.mm"
include "adantr.mm"
include "cn0.mm"
include "lencl.mm"
include "simplr.mm"
include "simprr.mm"
include "3jca.mm"
include "2ffzeq.mm"
include "syl.mm"
include "anbi12d.mm"
include "syl2anc.mm"
include "eqeq1.mm"
include "oveq2.mm"
include "raleqdv.mm"
include "bibi2d.mm"
include "3ad2ant3.mm"
include "mpbird.mm"
include "3anass.mm"
include "anandi.mm"
include "bitr2i.mm"
include "a1i.mm"
include "3bitrd.mm"

theorem wlkeq
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cG: class G
  let cN: class N

  disjoint A x
  disjoint B x
  disjoint N x
  assert |- ( ( A e. ( Walks ` G ) /\ B e. ( Walks ` G ) /\ N = ( # ` ( 1st ` A ) ) ) -> ( A = B <-> ( N = ( # ` ( 1st ` B ) ) /\ A. x e. ( 0 ..^ N ) ( ( 1st ` A ) ` x ) = ( ( 1st ` B ) ` x ) /\ A. x e. ( 0 ... N ) ( ( 2nd ` A ) ` x ) = ( ( 2nd ` B ) ` x ) ) ) )

  proof
    cA
    cG
    cwlks
    cfv
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cN
    cA
    c1st
    cfv
    #
    chash
    cfv
    #
    wceq
    #
    w3a
    #
    cA
    cB
    wceq
    #
    @3
    cB
    c1st
    cfv
    #
    wceq
    #
    cA
    c2nd
    cfv
    #
    cB
    c2nd
    cfv
    #
    wceq
    #
    wa
    #
    cN
    @8
    chash
    cfv
    #
    wceq
    #
    vx
    cv
    #
    @3
    cfv
    @16
    @8
    cfv
    wceq
    #
    vx
    cc0
    cN
    cfzo
    co
    #
    wral
    #
    wa
    #
    @15
    @16
    @10
    cfv
    @16
    @11
    cfv
    wceq
    #
    vx
    cc0
    cN
    cfz
    co
    #
    wral
    #
    wa
    #
    wa
    #
    @15
    @19
    @23
    w3a
    #
    @1
    @2
    @7
    @13
    wb
    #
    @5
    @1
    cA
    cvv
    cvv
    cxp
    #
    wcel
    #
    cB
    @28
    wcel
    #
    @27
    @2
    @1
    cA
    @3
    @10
    cop
    #
    wceq
    #
    @29
    cG
    cA
    wlkop
    #
    cA
    1st2ndb
    sylibr
    @2
    cB
    @8
    @11
    cop
    #
    wceq
    #
    @30
    cG
    cB
    wlkop
    #
    cB
    1st2ndb
    sylibr
    @29
    @30
    wa
    @13
    @7
    cA
    cB
    cvv
    cvv
    cvv
    cvv
    xpopth
    bicomd
    syl2an
    3adant3
    @6
    @13
    @25
    wb
    #
    @13
    @4
    @14
    wceq
    #
    @17
    vx
    cc0
    @4
    cfzo
    co
    #
    wral
    #
    wa
    #
    @38
    @21
    vx
    cc0
    @4
    cfz
    co
    #
    wral
    #
    wa
    #
    wa
    #
    wb
    #
    @1
    @2
    @46
    @5
    @1
    @2
    wa
    @3
    cG
    ciedg
    cfv
    #
    cdm
    #
    cword
    #
    wcel
    #
    @42
    cG
    cvtx
    cfv
    #
    @10
    wf
    #
    wa
    #
    @8
    @49
    wcel
    #
    cc0
    @14
    cfz
    co
    @51
    @11
    wf
    #
    wa
    #
    wa
    #
    @4
    @10
    chash
    cfv
    c1
    cmin
    co
    wceq
    #
    @14
    @11
    chash
    cfv
    c1
    cmin
    co
    wceq
    #
    wa
    #
    @46
    @1
    @53
    @2
    @56
    @10
    @3
    cG
    @47
    @51
    cA
    @51
    eqid
    #
    @47
    eqid
    #
    @3
    eqid
    @10
    eqid
    wlkelwrd
    @11
    @8
    cG
    @47
    @51
    cB
    @61
    @62
    @8
    eqid
    @11
    eqid
    wlkelwrd
    anim12i
    @1
    @58
    @2
    @59
    @32
    @1
    @58
    @33
    @32
    @1
    @31
    @0
    wcel
    #
    @58
    cA
    @31
    @0
    eleq1
    @63
    @3
    @10
    @0
    wbr
    @58
    @3
    @10
    @0
    df-br
    @10
    @3
    cG
    wlklenvm1
    sylbir
    syl6bi
    mpcom
    @35
    @2
    @59
    @36
    @35
    @2
    @34
    @0
    wcel
    #
    @59
    cB
    @34
    @0
    eleq1
    @64
    @8
    @11
    @0
    wbr
    @59
    @8
    @11
    @0
    df-br
    @11
    @8
    cG
    wlklenvm1
    sylbir
    syl6bi
    mpcom
    anim12i
    @57
    @60
    wa
    #
    @9
    @41
    @12
    @44
    @57
    @9
    @41
    wb
    #
    @60
    @50
    @54
    @66
    @52
    @55
    @3
    vx
    @48
    @8
    eqwrd
    ad2ant2r
    adantr
    @65
    @4
    cn0
    wcel
    #
    @52
    @55
    w3a
    #
    @12
    @44
    wb
    @57
    @68
    @60
    @57
    @67
    @52
    @55
    @53
    @67
    @56
    @50
    @67
    @52
    @48
    @3
    lencl
    adantr
    adantr
    @50
    @52
    @56
    simplr
    @53
    @54
    @55
    simprr
    3jca
    adantr
    @11
    vx
    @10
    @4
    @14
    @51
    @51
    2ffzeq
    syl
    anbi12d
    syl2anc
    3adant3
    @5
    @1
    @37
    @46
    wb
    @2
    @5
    @25
    @45
    @13
    @5
    @20
    @41
    @24
    @44
    @5
    @15
    @38
    @19
    @40
    cN
    @4
    @14
    eqeq1
    #
    @5
    @17
    vx
    @18
    @39
    cN
    @4
    cc0
    cfzo
    oveq2
    raleqdv
    anbi12d
    @5
    @15
    @38
    @23
    @43
    @69
    @5
    @21
    vx
    @22
    @42
    cN
    @4
    cc0
    cfz
    oveq2
    raleqdv
    anbi12d
    anbi12d
    bibi2d
    3ad2ant3
    mpbird
    @25
    @26
    wb
    @6
    @26
    @15
    @19
    @23
    wa
    wa
    @25
    @15
    @19
    @23
    3anass
    @15
    @19
    @23
    anandi
    bitr2i
    a1i
    3bitrd
end
