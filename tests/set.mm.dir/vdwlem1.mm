include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cvdwm.mm"
include "wbr.mm"
include "cv.mm"
include "cvdwa.mm"
include "cfv.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wss.mm"
include "cn.mm"
include "wrex.mm"
include "wex.mm"
include "wcel.mm"
include "cfz.mm"
include "ffvelrnd.mm"
include "cun.mm"
include "cn0.mm"
include "wceq.mm"
include "nnnn0d.mm"
include "vdwapun.mm"
include "syl3anc.mm"
include "cle.mm"
include "nnred.mm"
include "cuz.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "eluzfz1.mm"
include "syl.mm"
include "nnaddcld.mm"
include "nnrpd.mm"
include "ltaddrpd.mm"
include "ltled.mm"
include "wral.mm"
include "wa.mm"
include "r19.21bi.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wf.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "adantr.mm"
include "sstrd.mm"
include "cmul.mm"
include "cc0.mm"
include "cmin.mm"
include "nnm1nn0.mm"
include "nn0uz.mm"
include "ffvelrnda.mm"
include "nncnd.mm"
include "mul02d.mm"
include "oveq2d.mm"
include "addid1d.mm"
include "eqtr2d.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wb.mm"
include "vdwapval.mm"
include "mpbird.mm"
include "sseldd.mm"
include "ralrimiva.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "elfzle2.mm"
include "letrd.mm"
include "cz.mm"
include "nnzd.mm"
include "elfz5.mm"
include "eqidd.mm"
include "wfn.mm"
include "ffn.mm"
include "fniniseg.mm"
include "3syl.mm"
include "mpbir2and.mm"
include "snssd.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "sneqd.mm"
include "imaeq2d.mm"
include "sseq12d.mm"
include "sseqtr4d.mm"
include "unssd.mm"
include "eqsstrd.mm"
include "sseq1d.mm"
include "oveq2.mm"
include "rspc2ev.mm"
include "fvex.mm"
include "sneq.mm"
include "sseq2d.mm"
include "2rexbidv.mm"
include "spcev.mm"
include "ovex.mm"
include "peano2nn0.mm"
include "vdwmc.mm"

theorem vdwlem1
  let wph: wff ph
  let cA: class A
  let cD: class D
  let cR: class R
  let vi: setvar i
  let cF: class F
  let cI: class I
  let cK: class K
  let cM: class M
  let cW: class W
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let vm: setvar m
  assume vdwlem1.r: |- ( ph -> R e. Fin )
  assume vdwlem1.k: |- ( ph -> K e. NN )
  assume vdwlem1.w: |- ( ph -> W e. NN )
  assume vdwlem1.f: |- ( ph -> F : ( 1 ... W ) --> R )
  assume vdwlem1.a: |- ( ph -> A e. NN )
  assume vdwlem1.m: |- ( ph -> M e. NN )
  assume vdwlem1.d: |- ( ph -> D : ( 1 ... M ) --> NN )
  assume vdwlem1.s: |- ( ph -> A. i e. ( 1 ... M ) ( ( A + ( D ` i ) ) ( AP ` K ) ( D ` i ) ) C_ ( `' F " { ( F ` ( A + ( D ` i ) ) ) } ) )
  assume vdwlem1.i: |- ( ph -> I e. ( 1 ... M ) )
  assume vdwlem1.e: |- ( ph -> ( F ` A ) = ( F ` ( A + ( D ` I ) ) ) )

  disjoint A i
  disjoint D i
  disjoint I i
  disjoint K i
  disjoint F i
  disjoint M i
  disjoint i ph
  disjoint R i
  disjoint W i
  disjoint a c
  disjoint a d
  disjoint a i
  disjoint a m
  disjoint A a
  disjoint c d
  disjoint c i
  disjoint c m
  disjoint A c
  disjoint d i
  disjoint d m
  disjoint A d
  disjoint i m
  disjoint A m
  disjoint D d
  disjoint D m
  disjoint I d
  disjoint K a
  disjoint K c
  disjoint K d
  disjoint K m
  disjoint F a
  disjoint F c
  disjoint F d
  disjoint c ph
  assert |- ( ph -> ( K + 1 ) MonoAP F )

  proof
    wph
    cK
    c1
    caddc
    co
    #
    cF
    cvdwm
    wbr
    va
    cv
    #
    vd
    cv
    #
    @0
    cvdwa
    cfv
    #
    co
    #
    cF
    ccnv
    #
    vc
    cv
    #
    csn
    #
    cima
    #
    wss
    #
    vd
    cn
    wrex
    va
    cn
    wrex
    #
    vc
    wex
    #
    wph
    @4
    @5
    cA
    cF
    cfv
    #
    csn
    #
    cima
    #
    wss
    #
    vd
    cn
    wrex
    va
    cn
    wrex
    #
    @11
    wph
    cA
    cn
    wcel
    #
    cI
    cD
    cfv
    #
    cn
    wcel
    #
    cA
    @18
    @3
    co
    #
    @14
    wss
    #
    @16
    vdwlem1.a
    wph
    c1
    cM
    cfz
    co
    #
    cn
    cI
    cD
    vdwlem1.d
    vdwlem1.i
    ffvelrnd
    #
    wph
    @20
    cA
    csn
    #
    cA
    @18
    caddc
    co
    #
    @18
    cK
    cvdwa
    cfv
    #
    co
    #
    cun
    #
    @14
    wph
    cK
    cn0
    wcel
    #
    @17
    @19
    @20
    @28
    wceq
    wph
    cK
    vdwlem1.k
    nnnn0d
    #
    vdwlem1.a
    @23
    cA
    @18
    cK
    vdwapun
    syl3anc
    wph
    @24
    @27
    @14
    wph
    cA
    @14
    wph
    cA
    @14
    wcel
    #
    cA
    c1
    cW
    cfz
    co
    #
    wcel
    #
    @12
    @12
    wceq
    #
    wph
    @33
    cA
    cW
    cle
    wbr
    #
    wph
    cA
    cA
    c1
    cD
    cfv
    #
    caddc
    co
    #
    cW
    wph
    cA
    vdwlem1.a
    nnred
    #
    wph
    @37
    wph
    cA
    @36
    vdwlem1.a
    wph
    @22
    cn
    c1
    cD
    vdwlem1.d
    wph
    cM
    c1
    cuz
    cfv
    #
    wcel
    c1
    @22
    wcel
    #
    wph
    cM
    cn
    @39
    vdwlem1.m
    nnuz
    syl6eleq
    c1
    cM
    eluzfz1
    syl
    #
    ffvelrnd
    #
    nnaddcld
    nnred
    #
    wph
    cW
    vdwlem1.w
    nnred
    wph
    cA
    @37
    @38
    @43
    wph
    cA
    @36
    @38
    wph
    @36
    @42
    nnrpd
    ltaddrpd
    ltled
    wph
    @37
    @32
    wcel
    #
    @37
    cW
    cle
    wbr
    wph
    @40
    cA
    vi
    cv
    #
    cD
    cfv
    #
    caddc
    co
    #
    @32
    wcel
    #
    vi
    @22
    wral
    @44
    @41
    wph
    @48
    vi
    @22
    wph
    @45
    @22
    wcel
    #
    wa
    #
    @47
    @46
    @26
    co
    #
    @32
    @47
    @50
    @51
    @5
    @47
    cF
    cfv
    #
    csn
    #
    cima
    #
    @32
    wph
    @51
    @54
    wss
    #
    vi
    @22
    vdwlem1.s
    r19.21bi
    wph
    @54
    @32
    wss
    @49
    wph
    cF
    cdm
    #
    @54
    @32
    cF
    @53
    cnvimass
    wph
    @32
    cR
    cF
    wf
    #
    @56
    @32
    wceq
    vdwlem1.f
    @32
    cR
    cF
    fdm
    syl
    syl5sseq
    adantr
    sstrd
    @50
    @47
    @51
    wcel
    #
    @47
    @47
    vm
    cv
    #
    @46
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vm
    cc0
    cK
    c1
    cmin
    co
    #
    cfz
    co
    #
    wrex
    #
    @50
    cc0
    @64
    wcel
    #
    @47
    @47
    cc0
    @46
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @65
    wph
    @66
    @49
    wph
    @63
    cc0
    cuz
    cfv
    #
    wcel
    @66
    wph
    @63
    cn0
    @70
    wph
    cK
    cn
    wcel
    #
    @63
    cn0
    wcel
    vdwlem1.k
    cK
    nnm1nn0
    syl
    nn0uz
    syl6eleq
    cc0
    @63
    eluzfz1
    syl
    adantr
    @50
    @68
    @47
    cc0
    caddc
    co
    @47
    @50
    @67
    cc0
    @47
    caddc
    @50
    @46
    @50
    @46
    wph
    @22
    cn
    @45
    cD
    vdwlem1.d
    ffvelrnda
    #
    nncnd
    mul02d
    oveq2d
    @50
    @47
    @50
    @47
    @50
    cA
    @46
    wph
    @17
    @49
    vdwlem1.a
    adantr
    @72
    nnaddcld
    #
    nncnd
    addid1d
    eqtr2d
    @62
    @69
    vm
    cc0
    @64
    @59
    cc0
    wceq
    #
    @61
    @68
    @47
    @74
    @60
    @67
    @47
    caddc
    @59
    cc0
    @46
    cmul
    oveq1
    oveq2d
    eqeq2d
    rspcev
    syl2anc
    @50
    @29
    @47
    cn
    wcel
    @46
    cn
    wcel
    @58
    @65
    wb
    @50
    cK
    wph
    @71
    @49
    vdwlem1.k
    adantr
    nnnn0d
    @73
    @72
    @47
    @46
    vm
    cK
    @47
    vdwapval
    syl3anc
    mpbird
    sseldd
    ralrimiva
    @48
    @44
    vi
    c1
    @22
    @45
    c1
    wceq
    #
    @47
    @37
    @32
    @75
    @46
    @36
    cA
    caddc
    @45
    c1
    cD
    fveq2
    oveq2d
    eleq1d
    rspcv
    sylc
    @37
    c1
    cW
    elfzle2
    syl
    letrd
    wph
    cA
    @39
    wcel
    cW
    cz
    wcel
    @33
    @35
    wb
    wph
    cA
    cn
    @39
    vdwlem1.a
    nnuz
    syl6eleq
    wph
    cW
    vdwlem1.w
    nnzd
    cA
    c1
    cW
    elfz5
    syl2anc
    mpbird
    wph
    @12
    eqidd
    wph
    @57
    cF
    @32
    wfn
    @31
    @33
    @34
    wa
    wb
    vdwlem1.f
    @32
    cR
    cF
    ffn
    @32
    @12
    cA
    cF
    fniniseg
    3syl
    mpbir2and
    snssd
    wph
    @27
    @5
    @25
    cF
    cfv
    #
    csn
    #
    cima
    #
    @14
    wph
    cI
    @22
    wcel
    @55
    vi
    @22
    wral
    @27
    @78
    wss
    #
    vdwlem1.i
    vdwlem1.s
    @55
    @79
    vi
    cI
    @22
    @45
    cI
    wceq
    #
    @51
    @27
    @54
    @78
    @80
    @47
    @25
    @46
    @18
    @26
    @80
    @46
    @18
    cA
    caddc
    @45
    cI
    cD
    fveq2
    #
    oveq2d
    #
    @81
    oveq12d
    @80
    @53
    @77
    @5
    @80
    @52
    @76
    @80
    @47
    @25
    cF
    @82
    fveq2d
    sneqd
    imaeq2d
    sseq12d
    rspcv
    sylc
    wph
    @13
    @77
    @5
    wph
    @12
    @76
    vdwlem1.e
    sneqd
    imaeq2d
    sseqtr4d
    unssd
    eqsstrd
    @15
    @21
    cA
    @2
    @3
    co
    #
    @14
    wss
    va
    vd
    cA
    @18
    cn
    cn
    @1
    cA
    wceq
    @4
    @83
    @14
    @1
    cA
    @2
    @3
    oveq1
    sseq1d
    @2
    @18
    wceq
    @83
    @20
    @14
    @2
    @18
    cA
    @3
    oveq2
    sseq1d
    rspc2ev
    syl3anc
    @10
    @16
    vc
    @12
    cA
    cF
    fvex
    @6
    @12
    wceq
    #
    @9
    @15
    va
    vd
    cn
    cn
    @84
    @8
    @14
    @4
    @84
    @7
    @13
    @5
    @6
    @12
    sneq
    imaeq2d
    sseq2d
    2rexbidv
    spcev
    syl
    wph
    cR
    cF
    @0
    @32
    va
    vc
    vd
    c1
    cW
    cfz
    ovex
    wph
    @29
    @0
    cn0
    wcel
    @30
    cK
    peano2nn0
    syl
    vdwlem1.f
    vdwmc
    mpbird
end
