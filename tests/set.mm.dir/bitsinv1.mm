include "cn0.mm"
include "wcel.mm"
include "cbits.mm"
include "cfv.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cin.mm"
include "c2.mm"
include "cv.mm"
include "cexp.mm"
include "csu.mm"
include "cmo.mm"
include "wceq.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "c0.mm"
include "oveq2.mm"
include "fzo0.mm"
include "syl6eq.mm"
include "ineq2d.mm"
include "in0.mm"
include "sumeq1d.mm"
include "sum0.mm"
include "cc.mm"
include "2cn.mm"
include "exp0.mm"
include "ax-mp.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "cz.mm"
include "nn0z.mm"
include "zmod10.mm"
include "syl.mm"
include "eqcomd.mm"
include "wa.mm"
include "csn.mm"
include "oveq1.mm"
include "wn.mm"
include "fzonel.mm"
include "a1i.mm"
include "disjsn.mm"
include "sylibr.mm"
include "inindi.mm"
include "3eqtr3g.mm"
include "cun.mm"
include "cuz.mm"
include "simpr.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "fzosplitsn.mm"
include "indi.mm"
include "cfn.mm"
include "wss.mm"
include "fzofi.mm"
include "inss2.mm"
include "ssfi.mm"
include "mp2an.mm"
include "cn.mm"
include "2nn.mm"
include "elin2d.mm"
include "elfzouz.mm"
include "syl6eleqr.mm"
include "nnexpcld.mm"
include "nncnd.mm"
include "fsumsplit.mm"
include "cif.mm"
include "bitsinv1lem.mm"
include "sylan.mm"
include "eqeq2.mm"
include "snssd.mm"
include "sseqin2.mm"
include "sylib.mm"
include "simplr.mm"
include "sumsn.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "ifbothda.mm"
include "eqtr4d.mm"
include "syl5ibr.mm"
include "expcom.mm"
include "a2d.mm"
include "nn0ind.mm"
include "pm2.43i.mm"
include "clt.mm"
include "wbr.mm"
include "id.mm"
include "nnzd.mm"
include "2z.mm"
include "uzid.mm"
include "bernneq3.mm"
include "mpan.mm"
include "elfzo2.mm"
include "syl3anbrc.mm"
include "wb.mm"
include "bitsfzo.mm"
include "mpbid.mm"
include "df-ss.mm"
include "cr.mm"
include "crp.mm"
include "cle.mm"
include "nn0re.mm"
include "2rp.mm"
include "rpexpcld.mm"
include "nn0ge0.mm"
include "modid.mm"
include "syl22anc.mm"
include "3eqtr3d.mm"

theorem bitsinv1
  let vn: setvar n
  let cN: class N
  let vk: setvar k
  let vm: setvar m
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint N n
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint A m
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint k y
  disjoint N k
  disjoint n y
  disjoint x y
  disjoint N x
  disjoint N y
  assert |- ( N e. NN0 -> sum_ n e. ( bits ` N ) ( 2 ^ n ) = N )

  proof
    cN
    cn0
    wcel
    #
    cN
    cbits
    cfv
    #
    cc0
    cN
    cfzo
    co
    #
    cin
    #
    c2
    vn
    cv
    #
    cexp
    co
    #
    vn
    csu
    #
    cN
    c2
    cN
    cexp
    co
    #
    cmo
    co
    #
    @1
    @5
    vn
    csu
    cN
    @0
    @6
    @8
    wceq
    #
    @0
    @1
    cc0
    vx
    cv
    #
    cfzo
    co
    #
    cin
    #
    @5
    vn
    csu
    #
    cN
    c2
    @10
    cexp
    co
    #
    cmo
    co
    #
    wceq
    #
    wi
    @0
    cc0
    cN
    c1
    cmo
    co
    #
    wceq
    #
    wi
    @0
    @1
    cc0
    vk
    cv
    #
    cfzo
    co
    #
    cin
    #
    @5
    vn
    csu
    #
    cN
    c2
    @19
    cexp
    co
    #
    cmo
    co
    #
    wceq
    #
    wi
    @0
    @1
    cc0
    @19
    c1
    caddc
    co
    #
    cfzo
    co
    #
    cin
    #
    @5
    vn
    csu
    #
    cN
    c2
    @26
    cexp
    co
    #
    cmo
    co
    #
    wceq
    #
    wi
    @0
    @9
    wi
    vx
    vk
    cN
    @10
    cc0
    wceq
    #
    @16
    @18
    @0
    @33
    @13
    cc0
    @15
    @17
    @33
    @13
    c0
    @5
    vn
    csu
    #
    cc0
    @33
    @12
    c0
    @5
    vn
    @33
    @12
    @1
    c0
    cin
    #
    c0
    @33
    @11
    c0
    @1
    @33
    @11
    cc0
    cc0
    cfzo
    co
    c0
    @10
    cc0
    cc0
    cfzo
    oveq2
    cc0
    fzo0
    syl6eq
    ineq2d
    @1
    in0
    #
    syl6eq
    sumeq1d
    @5
    vn
    sum0
    #
    syl6eq
    @33
    @14
    c1
    cN
    cmo
    @33
    @14
    c2
    cc0
    cexp
    co
    #
    c1
    @10
    cc0
    c2
    cexp
    oveq2
    c2
    cc
    wcel
    @38
    c1
    wceq
    2cn
    c2
    exp0
    ax-mp
    syl6eq
    oveq2d
    eqeq12d
    imbi2d
    @10
    @19
    wceq
    #
    @16
    @25
    @0
    @39
    @13
    @22
    @15
    @24
    @39
    @12
    @21
    @5
    vn
    @39
    @11
    @20
    @1
    @10
    @19
    cc0
    cfzo
    oveq2
    ineq2d
    sumeq1d
    @39
    @14
    @23
    cN
    cmo
    @10
    @19
    c2
    cexp
    oveq2
    oveq2d
    eqeq12d
    imbi2d
    @10
    @26
    wceq
    #
    @16
    @32
    @0
    @40
    @13
    @29
    @15
    @31
    @40
    @12
    @28
    @5
    vn
    @40
    @11
    @27
    @1
    @10
    @26
    cc0
    cfzo
    oveq2
    ineq2d
    sumeq1d
    @40
    @14
    @30
    cN
    cmo
    @10
    @26
    c2
    cexp
    oveq2
    oveq2d
    eqeq12d
    imbi2d
    @10
    cN
    wceq
    #
    @16
    @9
    @0
    @41
    @13
    @6
    @15
    @8
    @41
    @12
    @3
    @5
    vn
    @41
    @11
    @2
    @1
    @10
    cN
    cc0
    cfzo
    oveq2
    ineq2d
    sumeq1d
    @41
    @14
    @7
    cN
    cmo
    @10
    cN
    c2
    cexp
    oveq2
    oveq2d
    eqeq12d
    imbi2d
    @0
    @17
    cc0
    @0
    cN
    cz
    wcel
    #
    @17
    cc0
    wceq
    cN
    nn0z
    #
    cN
    zmod10
    syl
    eqcomd
    @19
    cn0
    wcel
    #
    @0
    @25
    @32
    @0
    @44
    @25
    @32
    wi
    @25
    @32
    @0
    @44
    wa
    #
    @22
    @1
    @19
    csn
    #
    cin
    #
    @5
    vn
    csu
    #
    caddc
    co
    #
    @24
    @48
    caddc
    co
    #
    wceq
    @22
    @24
    @48
    caddc
    oveq1
    @45
    @29
    @49
    @31
    @50
    @45
    @21
    @47
    @5
    @28
    vn
    @45
    @1
    @20
    @46
    cin
    #
    cin
    @35
    @21
    @47
    cin
    c0
    @45
    @51
    c0
    @1
    @45
    @19
    @20
    wcel
    wn
    #
    @51
    c0
    wceq
    @52
    @45
    cc0
    @19
    fzonel
    a1i
    @20
    @19
    disjsn
    sylibr
    ineq2d
    @1
    @20
    @46
    inindi
    @36
    3eqtr3g
    @45
    @28
    @1
    @20
    @46
    cun
    #
    cin
    @21
    @47
    cun
    @45
    @27
    @53
    @1
    @45
    @19
    cc0
    cuz
    cfv
    #
    wcel
    @27
    @53
    wceq
    @45
    @19
    cn0
    @54
    @0
    @44
    simpr
    nn0uz
    syl6eleq
    cc0
    @19
    fzosplitsn
    syl
    ineq2d
    @1
    @20
    @46
    indi
    syl6eq
    @28
    cfn
    wcel
    #
    @45
    @27
    cfn
    wcel
    @28
    @27
    wss
    @55
    cc0
    @26
    fzofi
    @1
    @27
    inss2
    @27
    @28
    ssfi
    mp2an
    a1i
    @45
    @4
    @28
    wcel
    #
    wa
    #
    @5
    @57
    c2
    @4
    c2
    cn
    wcel
    #
    @57
    2nn
    a1i
    @57
    @4
    @54
    cn0
    @57
    @4
    @27
    wcel
    @4
    @54
    wcel
    @57
    @1
    @27
    @4
    @45
    @56
    simpr
    elin2d
    @4
    cc0
    @26
    elfzouz
    syl
    nn0uz
    syl6eleqr
    nnexpcld
    nncnd
    fsumsplit
    @45
    @31
    @24
    @19
    @1
    wcel
    #
    @23
    cc0
    cif
    #
    caddc
    co
    #
    @50
    @0
    @42
    @44
    @31
    @61
    wceq
    @43
    @19
    cN
    bitsinv1lem
    sylan
    @45
    @48
    @60
    @24
    caddc
    @59
    @48
    @23
    wceq
    @48
    cc0
    wceq
    @48
    @60
    wceq
    @45
    @23
    cc0
    @23
    @60
    @48
    eqeq2
    cc0
    @60
    @48
    eqeq2
    @45
    @59
    wa
    #
    @48
    @46
    @5
    vn
    csu
    #
    @23
    @62
    @47
    @46
    @5
    vn
    @62
    @46
    @1
    wss
    @47
    @46
    wceq
    @62
    @19
    @1
    @45
    @59
    simpr
    snssd
    @46
    @1
    sseqin2
    sylib
    sumeq1d
    @62
    @44
    @23
    cc
    wcel
    @63
    @23
    wceq
    @0
    @44
    @59
    simplr
    #
    @62
    @23
    @62
    c2
    @19
    @58
    @62
    2nn
    a1i
    @64
    nnexpcld
    nncnd
    @5
    @23
    vn
    @19
    cn0
    @4
    @19
    c2
    cexp
    oveq2
    sumsn
    syl2anc
    eqtrd
    @45
    @59
    wn
    #
    wa
    #
    @48
    @34
    cc0
    @66
    @47
    c0
    @5
    vn
    @66
    @65
    @47
    c0
    wceq
    @45
    @65
    simpr
    @1
    @19
    disjsn
    sylibr
    sumeq1d
    @37
    syl6eq
    ifbothda
    oveq2d
    eqtr4d
    eqeq12d
    syl5ibr
    expcom
    a2d
    nn0ind
    pm2.43i
    @0
    @3
    @1
    @5
    vn
    @0
    @1
    @2
    wss
    #
    @3
    @1
    wceq
    @0
    cN
    cc0
    @7
    cfzo
    co
    wcel
    #
    @67
    @0
    cN
    @54
    wcel
    @7
    cz
    wcel
    cN
    @7
    clt
    wbr
    #
    @68
    @0
    cN
    cn0
    @54
    @0
    id
    #
    nn0uz
    syl6eleq
    @0
    @7
    @0
    c2
    cN
    @58
    @0
    2nn
    a1i
    @70
    nnexpcld
    nnzd
    c2
    c2
    cuz
    cfv
    wcel
    #
    @0
    @69
    c2
    cz
    wcel
    @71
    2z
    c2
    uzid
    ax-mp
    c2
    cN
    bernneq3
    mpan
    #
    cN
    cc0
    @7
    elfzo2
    syl3anbrc
    @0
    @42
    @0
    @68
    @67
    wb
    @43
    @70
    cN
    cN
    bitsfzo
    syl2anc
    mpbid
    @1
    @2
    df-ss
    sylib
    sumeq1d
    @0
    cN
    cr
    wcel
    @7
    crp
    wcel
    cc0
    cN
    cle
    wbr
    @69
    @8
    cN
    wceq
    cN
    nn0re
    @0
    c2
    cN
    c2
    crp
    wcel
    @0
    2rp
    a1i
    @43
    rpexpcld
    cN
    nn0ge0
    @72
    cN
    @7
    modid
    syl22anc
    3eqtr3d
end
