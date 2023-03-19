include "csad.mm"
include "co.mm"
include "cc0.mm"
include "cfzo.mm"
include "cin.mm"
include "cbits.mm"
include "cn0.mm"
include "cres.mm"
include "ccnv.mm"
include "cfv.mm"
include "wceq.mm"
include "c2.mm"
include "cexp.mm"
include "cmo.mm"
include "caddc.mm"
include "inass.mm"
include "inidm.mm"
include "ineq2i.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "oveq12i.mm"
include "oveq1i.mm"
include "c2o.mm"
include "cv.mm"
include "wcel.mm"
include "c0.mm"
include "wcad.mm"
include "c1o.mm"
include "cif.mm"
include "cmpt2.mm"
include "c1.mm"
include "cmin.mm"
include "cmpt.mm"
include "cseq.mm"
include "inss1.mm"
include "syl5ss.mm"
include "eqid.mm"
include "sadadd3.mm"
include "3eqtr4a.mm"
include "cr.mm"
include "crp.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cpw.mm"
include "cfn.mm"
include "wss.mm"
include "sadcl.mm"
include "syl2anc.mm"
include "fzofi.mm"
include "a1i.mm"
include "inss2.mm"
include "ssfi.mm"
include "sylancl.mm"
include "elfpw.mm"
include "sylanbrc.mm"
include "wf1o.mm"
include "wf.mm"
include "bitsf1o.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "mp2b.mm"
include "ffvelrni.mm"
include "syl.mm"
include "nn0red.mm"
include "2rp.mm"
include "nn0zd.mm"
include "rpexpcld.mm"
include "nn0ge0d.mm"
include "fvres.mm"
include "f1ocnvfv2.mm"
include "sylancr.mm"
include "eqtr3d.mm"
include "syl6eqss.mm"
include "cz.mm"
include "wb.mm"
include "bitsfzo.mm"
include "mpbird.mm"
include "elfzolt2.mm"
include "modid.mm"
include "syl22anc.mm"
include "3eqtr3rd.mm"
include "wf1.mm"
include "wa.mm"
include "f1of1.mm"
include "f1fveq.mm"
include "mpan.mm"
include "mpbid.mm"

theorem sadeq
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cN: class N
  let vc: setvar c
  let vm: setvar m
  let vn: setvar n
  assume sadeq.a: |- ( ph -> A C_ NN0 )
  assume sadeq.b: |- ( ph -> B C_ NN0 )
  assume sadeq.n: |- ( ph -> N e. NN0 )


  assert |- ( ph -> ( ( A sadd B ) i^i ( 0 ..^ N ) ) = ( ( ( A i^i ( 0 ..^ N ) ) sadd ( B i^i ( 0 ..^ N ) ) ) i^i ( 0 ..^ N ) ) )

  proof
    wph
    cA
    cB
    csad
    co
    #
    cc0
    cN
    cfzo
    co
    #
    cin
    #
    cbits
    cn0
    cres
    #
    ccnv
    #
    cfv
    #
    cA
    @1
    cin
    #
    cB
    @1
    cin
    #
    csad
    co
    #
    @1
    cin
    #
    @4
    cfv
    #
    wceq
    #
    @2
    @9
    wceq
    #
    wph
    @10
    c2
    cN
    cexp
    co
    #
    cmo
    co
    #
    @5
    @13
    cmo
    co
    #
    @10
    @5
    wph
    @6
    @1
    cin
    #
    @4
    cfv
    #
    @7
    @1
    cin
    #
    @4
    cfv
    #
    caddc
    co
    #
    @13
    cmo
    co
    @6
    @4
    cfv
    #
    @7
    @4
    cfv
    #
    caddc
    co
    #
    @13
    cmo
    co
    @14
    @15
    @20
    @23
    @13
    cmo
    @17
    @21
    @19
    @22
    caddc
    @16
    @6
    @4
    @16
    cA
    @1
    @1
    cin
    #
    cin
    @6
    cA
    @1
    @1
    inass
    @24
    @1
    cA
    @1
    inidm
    #
    ineq2i
    eqtri
    fveq2i
    @18
    @7
    @4
    @18
    cB
    @24
    cin
    @7
    cB
    @1
    @1
    inass
    @24
    @1
    cB
    @25
    ineq2i
    eqtri
    fveq2i
    oveq12i
    oveq1i
    wph
    @6
    @7
    vc
    vm
    c2o
    cn0
    vm
    cv
    #
    @6
    wcel
    @26
    @7
    wcel
    c0
    vc
    cv
    wcel
    #
    wcad
    c1o
    c0
    cif
    cmpt2
    vn
    cn0
    vn
    cv
    #
    cc0
    wceq
    c0
    @28
    c1
    cmin
    co
    cif
    cmpt
    #
    cc0
    cseq
    #
    vm
    vn
    @4
    cN
    vc
    wph
    @6
    cA
    cn0
    cA
    @1
    inss1
    sadeq.a
    syl5ss
    #
    wph
    @7
    cB
    cn0
    cB
    @1
    inss1
    sadeq.b
    syl5ss
    #
    @30
    eqid
    sadeq.n
    @4
    eqid
    #
    sadadd3
    wph
    cA
    cB
    vc
    vm
    c2o
    cn0
    @26
    cA
    wcel
    @26
    cB
    wcel
    @27
    wcad
    c1o
    c0
    cif
    cmpt2
    @29
    cc0
    cseq
    #
    vm
    vn
    @4
    cN
    vc
    sadeq.a
    sadeq.b
    @34
    eqid
    sadeq.n
    @33
    sadadd3
    3eqtr4a
    wph
    @10
    cr
    wcel
    @13
    crp
    wcel
    #
    cc0
    @10
    cle
    wbr
    @10
    @13
    clt
    wbr
    #
    @14
    @10
    wceq
    wph
    @10
    wph
    @9
    cn0
    cpw
    cfn
    cin
    #
    wcel
    #
    @10
    cn0
    wcel
    #
    wph
    @9
    cn0
    wss
    @9
    cfn
    wcel
    #
    @38
    wph
    @9
    @8
    cn0
    @8
    @1
    inss1
    wph
    @6
    cn0
    wss
    @7
    cn0
    wss
    @8
    cn0
    wss
    @31
    @32
    @6
    @7
    sadcl
    syl2anc
    syl5ss
    wph
    @1
    cfn
    wcel
    #
    @9
    @1
    wss
    @40
    @41
    wph
    cc0
    cN
    fzofi
    a1i
    #
    @8
    @1
    inss2
    #
    @1
    @9
    ssfi
    sylancl
    @9
    cn0
    elfpw
    sylanbrc
    #
    @37
    cn0
    @9
    @4
    cn0
    @37
    @3
    wf1o
    #
    @37
    cn0
    @4
    wf1o
    #
    @37
    cn0
    @4
    wf
    bitsf1o
    cn0
    @37
    @3
    f1ocnv
    #
    @37
    cn0
    @4
    f1of
    mp2b
    #
    ffvelrni
    syl
    #
    nn0red
    wph
    c2
    cN
    c2
    crp
    wcel
    wph
    2rp
    a1i
    wph
    cN
    sadeq.n
    nn0zd
    rpexpcld
    #
    wph
    @10
    @49
    nn0ge0d
    wph
    @10
    cc0
    @13
    cfzo
    co
    #
    wcel
    #
    @36
    wph
    @52
    @10
    cbits
    cfv
    #
    @1
    wss
    #
    wph
    @53
    @9
    @1
    wph
    @10
    @3
    cfv
    #
    @53
    @9
    wph
    @39
    @55
    @53
    wceq
    @49
    @10
    cn0
    cbits
    fvres
    syl
    wph
    @45
    @38
    @55
    @9
    wceq
    bitsf1o
    @44
    cn0
    @37
    @9
    @3
    f1ocnvfv2
    sylancr
    eqtr3d
    @43
    syl6eqss
    wph
    @10
    cz
    wcel
    cN
    cn0
    wcel
    #
    @52
    @54
    wb
    wph
    @10
    @49
    nn0zd
    sadeq.n
    cN
    @10
    bitsfzo
    syl2anc
    mpbird
    @10
    cc0
    @13
    elfzolt2
    syl
    @10
    @13
    modid
    syl22anc
    wph
    @5
    cr
    wcel
    @35
    cc0
    @5
    cle
    wbr
    @5
    @13
    clt
    wbr
    #
    @15
    @5
    wceq
    wph
    @5
    wph
    @2
    @37
    wcel
    #
    @5
    cn0
    wcel
    #
    wph
    @2
    cn0
    wss
    @2
    cfn
    wcel
    #
    @58
    wph
    @2
    @0
    cn0
    @0
    @1
    inss1
    wph
    cA
    cn0
    wss
    cB
    cn0
    wss
    @0
    cn0
    wss
    sadeq.a
    sadeq.b
    cA
    cB
    sadcl
    syl2anc
    syl5ss
    wph
    @41
    @2
    @1
    wss
    @60
    @42
    @0
    @1
    inss2
    #
    @1
    @2
    ssfi
    sylancl
    @2
    cn0
    elfpw
    sylanbrc
    #
    @37
    cn0
    @2
    @4
    @48
    ffvelrni
    syl
    #
    nn0red
    @50
    wph
    @5
    @63
    nn0ge0d
    wph
    @5
    @51
    wcel
    #
    @57
    wph
    @64
    @5
    cbits
    cfv
    #
    @1
    wss
    #
    wph
    @65
    @2
    @1
    wph
    @5
    @3
    cfv
    #
    @65
    @2
    wph
    @59
    @67
    @65
    wceq
    @63
    @5
    cn0
    cbits
    fvres
    syl
    wph
    @45
    @58
    @67
    @2
    wceq
    bitsf1o
    @62
    cn0
    @37
    @2
    @3
    f1ocnvfv2
    sylancr
    eqtr3d
    @61
    syl6eqss
    wph
    @5
    cz
    wcel
    @56
    @64
    @66
    wb
    wph
    @5
    @63
    nn0zd
    sadeq.n
    cN
    @5
    bitsfzo
    syl2anc
    mpbird
    @5
    cc0
    @13
    elfzolt2
    syl
    @5
    @13
    modid
    syl22anc
    3eqtr3rd
    wph
    @58
    @38
    @11
    @12
    wb
    #
    @62
    @44
    @37
    cn0
    @4
    wf1
    #
    @58
    @38
    wa
    @68
    @45
    @46
    @69
    bitsf1o
    @47
    @37
    cn0
    @4
    f1of1
    mp2b
    @37
    cn0
    @2
    @9
    @4
    f1fveq
    mpan
    syl2anc
    mpbid
end
