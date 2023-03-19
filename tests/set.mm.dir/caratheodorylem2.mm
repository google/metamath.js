include "cn.mm"
include "cv.mm"
include "cfv.mm"
include "ciun.mm"
include "cmpt.mm"
include "csumge0.mm"
include "wss.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "cuni.mm"
include "come.mm"
include "caragenss.mm"
include "syl.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "sseldd.mm"
include "elssuni.mm"
include "syl6sseqr.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "omexrcl.mm"
include "cvv.mm"
include "nnex.mm"
include "a1i.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "omecl.mm"
include "eqid.mm"
include "fmptd.mm"
include "sge0xrcl.mm"
include "c1.mm"
include "nfv.mm"
include "nfcv.mm"
include "nnuz.mm"
include "cpw.mm"
include "caragensspw.mm"
include "fssd.mm"
include "omeiunle.mm"
include "cle.mm"
include "wbr.mm"
include "cres.mm"
include "cfn.mm"
include "cin.mm"
include "wceq.mm"
include "elpwinss.mm"
include "resmptd.mm"
include "fveq2d.mm"
include "adantl.mm"
include "cfz.mm"
include "wrex.mm"
include "1zzd.mm"
include "elinel2.mm"
include "uzfissfz.mm"
include "wi.mm"
include "w3a.mm"
include "cxr.mm"
include "vex.mm"
include "ad2antrr.mm"
include "wf.mm"
include "fz1ssnn.mm"
include "ssel2.mm"
include "sseldi.mm"
include "adantll.mm"
include "ffvelrnd.mm"
include "elpwi.mm"
include "3adant2.mm"
include "ovex.mm"
include "elfznn.mm"
include "sylan2.mm"
include "3ad2ant1.mm"
include "simpl1.mm"
include "syl2anc.mm"
include "simp3.mm"
include "sge0lessmpt.mm"
include "wdisj.mm"
include "nfiu1.mm"
include "fveq2.mm"
include "cbviunv.mm"
include "oveq2.mm"
include "iuneq1d.mm"
include "eqtrd.mm"
include "cbvmpt.mm"
include "eqtri.mm"
include "cuz.mm"
include "id.mm"
include "syl6eleq.mm"
include "caratheodorylem1.mm"
include "eqcomd.mm"
include "fvex.mm"
include "iunex.mm"
include "fvmpt2.mm"
include "sylancl.mm"
include "iunss1.mm"
include "eqsstrd.mm"
include "omessle.mm"
include "eqbrtrd.mm"
include "3adant3.mm"
include "xrletrd.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "sge0lefi.mm"
include "mpbird.mm"
include "xrletrid.mm"

theorem caratheodorylem2
  let wph: wff ph
  let cS: class S
  let vk: setvar k
  let vn: setvar n
  let cE: class E
  let cG: class G
  let cO: class O
  let cX: class X
  let vm: setvar m
  let vx: setvar x
  assume caratheodorylem2.o: |- ( ph -> O e. OutMeas )
  assume caratheodorylem2.x: |- X = U. dom O
  assume caratheodorylem2.s: |- S = ( CaraGen ` O )
  assume caratheodorylem2.e: |- ( ph -> E : NN --> S )
  assume caratheodorylem2.5: |- ( ph -> Disj_ n e. NN ( E ` n ) )
  assume caratheodorylem2.g: |- G = ( k e. NN |-> U_ n e. ( 1 ... k ) ( E ` n ) )

  disjoint E k
  disjoint E n
  disjoint k n
  disjoint G n
  disjoint O k
  disjoint O n
  disjoint X n
  disjoint k ph
  disjoint n ph
  disjoint E m
  disjoint k m
  disjoint m n
  disjoint E x
  disjoint k x
  disjoint n x
  disjoint G m
  disjoint O m
  disjoint O x
  disjoint m ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( O ` U_ n e. NN ( E ` n ) ) = ( sum^ ` ( n e. NN |-> ( O ` ( E ` n ) ) ) ) )

  proof
    wph
    vn
    cn
    vn
    cv
    #
    cE
    cfv
    #
    ciun
    #
    cO
    cfv
    #
    vn
    cn
    @1
    cO
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    wph
    @2
    cO
    cX
    caratheodorylem2.o
    caratheodorylem2.x
    wph
    @1
    cX
    wss
    #
    vn
    cn
    wral
    @2
    cX
    wss
    #
    wph
    @7
    vn
    cn
    wph
    @0
    cn
    wcel
    #
    wa
    #
    @1
    cO
    cdm
    #
    cuni
    #
    cX
    @10
    @1
    @11
    wcel
    @1
    @12
    wss
    @10
    cS
    @11
    @1
    wph
    cS
    @11
    wss
    #
    @9
    wph
    cO
    come
    wcel
    #
    @13
    caratheodorylem2.o
    cS
    cO
    caratheodorylem2.s
    caragenss
    syl
    adantr
    wph
    cn
    cS
    @0
    cE
    caratheodorylem2.e
    ffvelrnda
    sseldd
    @1
    @11
    elssuni
    syl
    caratheodorylem2.x
    syl6sseqr
    #
    ralrimiva
    vn
    cn
    @1
    cX
    iunss
    sylibr
    #
    omexrcl
    #
    wph
    @5
    cvv
    cn
    cn
    cvv
    wcel
    wph
    nnex
    a1i
    #
    wph
    vn
    cn
    @4
    cc0
    cpnf
    cicc
    co
    #
    @5
    @10
    @1
    cO
    cX
    wph
    @14
    @9
    caratheodorylem2.o
    adantr
    caratheodorylem2.x
    @15
    omecl
    #
    @5
    eqid
    fmptd
    #
    sge0xrcl
    wph
    vn
    cE
    c1
    cO
    cX
    cn
    wph
    vn
    nfv
    vn
    cE
    nfcv
    caratheodorylem2.o
    caratheodorylem2.x
    nnuz
    wph
    cn
    cS
    cX
    cpw
    #
    cE
    caratheodorylem2.e
    wph
    cS
    cO
    cX
    caratheodorylem2.o
    caratheodorylem2.x
    caratheodorylem2.s
    caragensspw
    fssd
    #
    omeiunle
    wph
    @6
    @3
    cle
    wbr
    @5
    vx
    cv
    #
    cres
    #
    csumge0
    cfv
    #
    @3
    cle
    wbr
    #
    vx
    cn
    cpw
    #
    cfn
    cin
    #
    wral
    wph
    @27
    vx
    @29
    wph
    @24
    @29
    wcel
    #
    wa
    #
    @26
    vn
    @24
    @4
    cmpt
    #
    csumge0
    cfv
    #
    @3
    cle
    @30
    @26
    @33
    wceq
    wph
    @30
    @25
    @32
    csumge0
    @30
    vn
    cn
    @24
    @4
    @24
    cn
    cfn
    elpwinss
    #
    resmptd
    fveq2d
    adantl
    @31
    @24
    c1
    vk
    cv
    #
    cfz
    co
    #
    wss
    #
    vk
    cn
    wrex
    @33
    @3
    cle
    wbr
    #
    @31
    @24
    vk
    c1
    cn
    @31
    1zzd
    nnuz
    @30
    @24
    cn
    wss
    wph
    @34
    adantl
    @30
    @24
    cfn
    wcel
    wph
    @24
    @28
    cfn
    elinel2
    adantl
    uzfissfz
    @31
    @37
    @38
    vk
    cn
    wph
    @35
    cn
    wcel
    #
    @37
    @38
    wi
    wi
    @30
    wph
    @39
    @37
    @38
    wph
    @39
    @37
    w3a
    #
    @33
    vn
    @36
    @4
    cmpt
    #
    csumge0
    cfv
    #
    @3
    wph
    @37
    @33
    cxr
    wcel
    @39
    wph
    @37
    wa
    #
    @32
    cvv
    @24
    @24
    cvv
    wcel
    @43
    vx
    vex
    a1i
    @43
    vn
    @24
    @4
    @19
    @32
    @43
    @0
    @24
    wcel
    #
    wa
    #
    @1
    cO
    cX
    wph
    @14
    @37
    @44
    caratheodorylem2.o
    ad2antrr
    caratheodorylem2.x
    @45
    @1
    @22
    wcel
    @7
    @45
    cn
    @22
    @0
    cE
    wph
    cn
    @22
    cE
    wf
    @37
    @44
    @23
    ad2antrr
    @37
    @44
    @9
    wph
    @37
    @44
    wa
    @36
    cn
    @0
    @35
    fz1ssnn
    #
    @24
    @36
    @0
    ssel2
    sseldi
    adantll
    ffvelrnd
    @1
    cX
    elpwi
    syl
    omecl
    @32
    eqid
    fmptd
    sge0xrcl
    3adant2
    wph
    @39
    @42
    cxr
    wcel
    @37
    wph
    @41
    cvv
    @36
    @36
    cvv
    wcel
    #
    wph
    c1
    @35
    cfz
    ovex
    #
    a1i
    wph
    vn
    @36
    @4
    @19
    @41
    @0
    @36
    wcel
    #
    wph
    @9
    @4
    @19
    wcel
    #
    @0
    @35
    elfznn
    #
    @20
    sylan2
    @41
    eqid
    fmptd
    sge0xrcl
    3ad2ant1
    wph
    @39
    @3
    cxr
    wcel
    @37
    @17
    3ad2ant1
    @40
    vn
    @36
    @4
    @24
    cvv
    @47
    @40
    @48
    a1i
    @40
    @49
    wa
    wph
    @9
    @50
    wph
    @39
    @37
    @49
    simpl1
    @49
    @9
    @40
    @51
    adantl
    @20
    syl2anc
    wph
    @39
    @37
    simp3
    sge0lessmpt
    wph
    @39
    @42
    @3
    cle
    wbr
    @37
    wph
    @39
    wa
    #
    @42
    @35
    cG
    cfv
    #
    cO
    cfv
    #
    @3
    cle
    @52
    @54
    @42
    @52
    cS
    vm
    vn
    cE
    cG
    c1
    @35
    cO
    cn
    wph
    @14
    @39
    caratheodorylem2.o
    adantr
    #
    caratheodorylem2.s
    nnuz
    wph
    cn
    cS
    cE
    wf
    @39
    caratheodorylem2.e
    adantr
    wph
    vn
    cn
    @1
    wdisj
    @39
    caratheodorylem2.5
    adantr
    cG
    vk
    cn
    vn
    @36
    @1
    ciun
    #
    cmpt
    vn
    cn
    vm
    c1
    @0
    cfz
    co
    #
    vm
    cv
    #
    cE
    cfv
    #
    ciun
    #
    cmpt
    caratheodorylem2.g
    vk
    vn
    cn
    @56
    @60
    vn
    @36
    @1
    nfiu1
    vk
    @60
    nfcv
    @35
    @0
    wceq
    #
    @56
    vm
    @36
    @59
    ciun
    #
    @60
    @56
    @62
    wceq
    @61
    vn
    vm
    @36
    @1
    @59
    @0
    @58
    cE
    fveq2
    cbviunv
    a1i
    @61
    vm
    @36
    @57
    @59
    @35
    @0
    c1
    cfz
    oveq2
    iuneq1d
    eqtrd
    cbvmpt
    eqtri
    @39
    @35
    c1
    cuz
    cfv
    #
    wcel
    wph
    @39
    @35
    cn
    @63
    @39
    id
    #
    nnuz
    syl6eleq
    adantl
    caratheodorylem1
    eqcomd
    @52
    @53
    @2
    cO
    cX
    @55
    caratheodorylem2.x
    wph
    @8
    @39
    @16
    adantr
    @39
    @53
    @2
    wss
    wph
    @39
    @53
    @56
    @2
    @39
    @39
    @56
    cvv
    wcel
    @53
    @56
    wceq
    @64
    vn
    @36
    @1
    @48
    @0
    cE
    fvex
    iunex
    vk
    cn
    @56
    cvv
    cG
    caratheodorylem2.g
    fvmpt2
    sylancl
    @39
    @36
    cn
    wss
    #
    @56
    @2
    wss
    @65
    @39
    @46
    a1i
    vn
    @36
    cn
    @1
    iunss1
    syl
    eqsstrd
    adantl
    omessle
    eqbrtrd
    3adant3
    xrletrd
    3exp
    adantr
    rexlimdv
    mpd
    eqbrtrd
    ralrimiva
    wph
    vx
    @3
    @5
    cvv
    cn
    @18
    @21
    @17
    sge0lefi
    mpbird
    xrletrid
end
