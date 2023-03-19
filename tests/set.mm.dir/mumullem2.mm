include "cn.mm"
include "wcel.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "w3a.mm"
include "cmu.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cmul.mm"
include "cv.mm"
include "cpc.mm"
include "cle.mm"
include "wbr.mm"
include "cprime.mm"
include "wral.mm"
include "r19.26.mm"
include "caddc.mm"
include "cr.mm"
include "wi.mm"
include "simpr.mm"
include "simpl1.mm"
include "pccld.mm"
include "nn0red.mm"
include "simpl2.mm"
include "1red.mm"
include "le2add.mm"
include "syl22anc.mm"
include "cmin.mm"
include "wn.mm"
include "ax-1ne0.mm"
include "cif.mm"
include "simpl3.mm"
include "oveq2d.mm"
include "cz.mm"
include "nnzd.mm"
include "pcgcd.mm"
include "syl3anc.mm"
include "pc1.mm"
include "adantl.mm"
include "3eqtr3d.mm"
include "ifid.mm"
include "ifeq12.mm"
include "syl5eqr.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "necon3ad.mm"
include "mpi.mm"
include "cc.mm"
include "wb.mm"
include "ax-1cn.mm"
include "recnd.mm"
include "subeq0.mm"
include "sylancr.mm"
include "anbi12d.mm"
include "mtbird.mm"
include "adantr.mm"
include "eqcom.mm"
include "1re.mm"
include "readdcli.mm"
include "recni.mm"
include "nn0addcld.mm"
include "syl6bb.mm"
include "addsub4d.mm"
include "bitr3d.mm"
include "subge0.mm"
include "resubcl.mm"
include "add20.mm"
include "an4s.mm"
include "ex.mm"
include "syl2anc.mm"
include "sylbird.mm"
include "imp.mm"
include "bitrd.mm"
include "syl5bb.mm"
include "necon3abid.mm"
include "mpbird.mm"
include "jcad.mm"
include "clt.mm"
include "nnz.mm"
include "nnne0.mm"
include "jca.mm"
include "syl.mm"
include "pcmul.mm"
include "breq1d.mm"
include "cn0.mm"
include "1nn0.mm"
include "nn0leltp1.mm"
include "sylancl.mm"
include "ltlen.mm"
include "3bitrd.mm"
include "sylibrd.mm"
include "ralimdva.mm"
include "syl5bir.mm"
include "issqf.mm"
include "bi2anan9.mm"
include "3adant3.mm"
include "nnmulcl.mm"
include "3imtr4d.mm"

theorem mumullem2
  let cA: class A
  let cB: class B
  let vp: setvar p


  assert |- ( ( ( A e. NN /\ B e. NN /\ ( A gcd B ) = 1 ) /\ ( ( mmu ` A ) =/= 0 /\ ( mmu ` B ) =/= 0 ) ) -> ( mmu ` ( A x. B ) ) =/= 0 )

  proof
    cA
    cn
    wcel
    #
    cB
    cn
    wcel
    #
    cA
    cB
    cgcd
    co
    #
    c1
    wceq
    #
    w3a
    #
    cA
    cmu
    cfv
    cc0
    wne
    #
    cB
    cmu
    cfv
    cc0
    wne
    #
    wa
    #
    cA
    cB
    cmul
    co
    #
    cmu
    cfv
    cc0
    wne
    #
    @4
    vp
    cv
    #
    cA
    cpc
    co
    #
    c1
    cle
    wbr
    #
    vp
    cprime
    wral
    #
    @10
    cB
    cpc
    co
    #
    c1
    cle
    wbr
    #
    vp
    cprime
    wral
    #
    wa
    #
    @10
    @8
    cpc
    co
    #
    c1
    cle
    wbr
    #
    vp
    cprime
    wral
    #
    @7
    @9
    @17
    @12
    @15
    wa
    #
    vp
    cprime
    wral
    @4
    @20
    @12
    @15
    vp
    cprime
    r19.26
    @4
    @21
    @19
    vp
    cprime
    @4
    @10
    cprime
    wcel
    #
    wa
    #
    @21
    @11
    @14
    caddc
    co
    #
    c1
    c1
    caddc
    co
    #
    cle
    wbr
    #
    @25
    @24
    wne
    #
    wa
    #
    @19
    @23
    @21
    @26
    @27
    @23
    @11
    cr
    wcel
    #
    @14
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    @31
    @21
    @26
    wi
    @23
    @11
    @23
    @10
    cA
    @4
    @22
    simpr
    #
    @0
    @1
    @3
    @22
    simpl1
    #
    pccld
    #
    nn0red
    #
    @23
    @14
    @23
    @10
    cB
    @32
    @0
    @1
    @3
    @22
    simpl2
    #
    pccld
    #
    nn0red
    #
    @23
    1red
    #
    @39
    @11
    @14
    c1
    c1
    le2add
    syl22anc
    @23
    @21
    @27
    @23
    @21
    wa
    #
    @27
    c1
    @11
    cmin
    co
    #
    cc0
    wceq
    #
    c1
    @14
    cmin
    co
    #
    cc0
    wceq
    #
    wa
    #
    wn
    #
    @23
    @46
    @21
    @23
    @45
    c1
    @11
    wceq
    #
    c1
    @14
    wceq
    #
    wa
    #
    @23
    c1
    cc0
    wne
    @49
    wn
    ax-1ne0
    @23
    @49
    c1
    cc0
    @23
    c1
    cc0
    wceq
    @49
    @11
    @14
    cle
    wbr
    #
    @11
    @14
    cif
    #
    cc0
    wceq
    @23
    @10
    @2
    cpc
    co
    #
    @10
    c1
    cpc
    co
    #
    @51
    cc0
    @23
    @2
    c1
    @10
    cpc
    @0
    @1
    @3
    @22
    simpl3
    oveq2d
    @23
    @22
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    @52
    @51
    wceq
    @32
    @23
    cA
    @33
    nnzd
    @23
    cB
    @36
    nnzd
    cA
    cB
    @10
    pcgcd
    syl3anc
    @22
    @53
    cc0
    wceq
    @4
    @10
    pc1
    adantl
    3eqtr3d
    @49
    c1
    @51
    cc0
    @49
    c1
    @50
    c1
    c1
    cif
    @51
    @50
    c1
    ifid
    @50
    c1
    @11
    c1
    @14
    ifeq12
    syl5eqr
    eqeq1d
    syl5ibrcom
    necon3ad
    mpi
    @23
    @42
    @47
    @44
    @48
    @23
    c1
    cc
    wcel
    #
    @11
    cc
    wcel
    @42
    @47
    wb
    ax-1cn
    @23
    @11
    @35
    recnd
    #
    c1
    @11
    subeq0
    sylancr
    @23
    @56
    @14
    cc
    wcel
    @44
    @48
    wb
    ax-1cn
    @23
    @14
    @38
    recnd
    #
    c1
    @14
    subeq0
    sylancr
    anbi12d
    mtbird
    adantr
    @40
    @45
    @25
    @24
    @25
    @24
    wceq
    #
    @24
    @25
    wceq
    #
    @40
    @45
    @25
    @24
    eqcom
    #
    @40
    @60
    @41
    @43
    caddc
    co
    #
    cc0
    wceq
    #
    @45
    @23
    @60
    @63
    wb
    @21
    @23
    @25
    @24
    cmin
    co
    #
    cc0
    wceq
    #
    @60
    @63
    @23
    @65
    @59
    @60
    @23
    @25
    cc
    wcel
    @24
    cc
    wcel
    @65
    @59
    wb
    @25
    c1
    c1
    1re
    1re
    readdcli
    #
    recni
    @23
    @24
    @23
    @24
    @23
    @11
    @14
    @34
    @37
    nn0addcld
    #
    nn0red
    #
    recnd
    @25
    @24
    subeq0
    sylancr
    @61
    syl6bb
    @23
    @64
    @62
    cc0
    @23
    c1
    c1
    @11
    @14
    @23
    c1
    @39
    recnd
    #
    @69
    @57
    @58
    addsub4d
    eqeq1d
    bitr3d
    adantr
    @23
    @21
    @63
    @45
    wb
    #
    @23
    @21
    cc0
    @41
    cle
    wbr
    #
    cc0
    @43
    cle
    wbr
    #
    wa
    #
    @70
    @23
    @71
    @12
    @72
    @15
    @23
    @31
    @29
    @71
    @12
    wb
    1re
    @35
    c1
    @11
    subge0
    sylancr
    @23
    @31
    @30
    @72
    @15
    wb
    1re
    @38
    c1
    @14
    subge0
    sylancr
    anbi12d
    @23
    @41
    cr
    wcel
    #
    @43
    cr
    wcel
    #
    @73
    @70
    wi
    @23
    @31
    @29
    @74
    1re
    @35
    c1
    @11
    resubcl
    sylancr
    @23
    @31
    @30
    @75
    1re
    @38
    c1
    @14
    resubcl
    sylancr
    @74
    @75
    wa
    @73
    @70
    @74
    @71
    @75
    @72
    @70
    @41
    @43
    add20
    an4s
    ex
    syl2anc
    sylbird
    imp
    bitrd
    syl5bb
    necon3abid
    mpbird
    ex
    jcad
    @23
    @19
    @24
    c1
    cle
    wbr
    #
    @24
    @25
    clt
    wbr
    #
    @28
    @23
    @18
    @24
    c1
    cle
    @23
    @22
    @54
    cA
    cc0
    wne
    #
    wa
    #
    @55
    cB
    cc0
    wne
    #
    wa
    #
    @18
    @24
    wceq
    @32
    @23
    @0
    @79
    @33
    @0
    @54
    @78
    cA
    nnz
    cA
    nnne0
    jca
    syl
    @23
    @1
    @81
    @36
    @1
    @55
    @80
    cB
    nnz
    cB
    nnne0
    jca
    syl
    cA
    cB
    @10
    pcmul
    syl3anc
    breq1d
    @23
    @24
    cn0
    wcel
    c1
    cn0
    wcel
    @76
    @77
    wb
    @67
    1nn0
    @24
    c1
    nn0leltp1
    sylancl
    @23
    @24
    cr
    wcel
    @25
    cr
    wcel
    @77
    @28
    wb
    @68
    @66
    @24
    @25
    ltlen
    sylancl
    3bitrd
    sylibrd
    ralimdva
    syl5bir
    @0
    @1
    @7
    @17
    wb
    @3
    @0
    @5
    @13
    @1
    @6
    @16
    cA
    vp
    issqf
    cB
    vp
    issqf
    bi2anan9
    3adant3
    @4
    @8
    cn
    wcel
    #
    @9
    @20
    wb
    @0
    @1
    @82
    @3
    cA
    cB
    nnmulcl
    3adant3
    @8
    vp
    issqf
    syl
    3imtr4d
    imp
end
