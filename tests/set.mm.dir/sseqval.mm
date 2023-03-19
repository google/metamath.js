include "cvv.mm"
include "cv.mm"
include "clsw.mm"
include "cfv.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "cmpt2.mm"
include "cn0.mm"
include "csn.mm"
include "cxp.mm"
include "chash.mm"
include "cseq.mm"
include "ccom.mm"
include "cun.mm"
include "csseq.mm"
include "wceq.mm"
include "df-sseq.mm"
include "a1i.mm"
include "wa.mm"
include "simprl.mm"
include "fveq2d.mm"
include "wcel.mm"
include "w3a.mm"
include "simp1rr.mm"
include "fveq1d.mm"
include "s1eqd.mm"
include "oveq2d.mm"
include "mpt2eq3dva.mm"
include "simprr.mm"
include "fveq12d.mm"
include "oveq12d.mm"
include "sneqd.mm"
include "xpeq2d.mm"
include "seqeq123d.mm"
include "coeq2d.mm"
include "uneq12d.mm"
include "cword.mm"
include "elex.mm"
include "syl.mm"
include "wf.mm"
include "ccnv.mm"
include "cuz.mm"
include "cima.mm"
include "cin.mm"
include "wrdexg.mm"
include "inex1g.mm"
include "3syl.mm"
include "syl5eqel.mm"
include "fex.mm"
include "syl2anc.mm"
include "wfun.mm"
include "c1.mm"
include "cmin.mm"
include "df-lsw.mm"
include "funmpt2.mm"
include "seqex.mm"
include "cofunexg.mm"
include "unexg.mm"
include "ovmpt2d.mm"

theorem sseqval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cF: class F
  let cM: class M
  let cW: class W
  let vf: setvar f
  let vm: setvar m
  assume sseqval.1: |- ( ph -> S e. _V )
  assume sseqval.2: |- ( ph -> M e. Word S )
  assume sseqval.3: |- W = ( Word S i^i ( `' # " ( ZZ>= ` ( # ` M ) ) ) )
  assume sseqval.4: |- ( ph -> F : W --> S )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint M x
  disjoint M y
  disjoint ph x
  disjoint ph y
  disjoint f m
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint m x
  disjoint m y
  disjoint F m
  disjoint M f
  disjoint M m
  disjoint f ph
  disjoint m ph
  assert |- ( ph -> ( M seqstr F ) = ( M u. ( lastS o. seq ( # ` M ) ( ( x e. _V , y e. _V |-> ( x ++ <" ( F ` x ) "> ) ) , ( NN0 X. { ( M ++ <" ( F ` M ) "> ) } ) ) ) ) )

  proof
    wph
    vm
    vf
    cM
    cF
    cvv
    cvv
    vm
    cv
    #
    clsw
    vx
    vy
    cvv
    cvv
    vx
    cv
    #
    @1
    vf
    cv
    #
    cfv
    #
    cs1
    #
    cconcat
    co
    #
    cmpt2
    #
    cn0
    @0
    @0
    @2
    cfv
    #
    cs1
    #
    cconcat
    co
    #
    csn
    #
    cxp
    #
    @0
    chash
    cfv
    #
    cseq
    #
    ccom
    #
    cun
    #
    cM
    clsw
    vx
    vy
    cvv
    cvv
    @1
    @1
    cF
    cfv
    #
    cs1
    #
    cconcat
    co
    #
    cmpt2
    #
    cn0
    cM
    cM
    cF
    cfv
    #
    cs1
    #
    cconcat
    co
    #
    csn
    #
    cxp
    #
    cM
    chash
    cfv
    #
    cseq
    #
    ccom
    #
    cun
    #
    csseq
    cvv
    csseq
    vm
    vf
    cvv
    cvv
    @15
    cmpt2
    wceq
    wph
    vx
    vy
    vf
    vm
    df-sseq
    a1i
    wph
    @0
    cM
    wceq
    #
    @2
    cF
    wceq
    #
    wa
    wa
    #
    @0
    cM
    @14
    @27
    wph
    @29
    @30
    simprl
    #
    @31
    @13
    @26
    clsw
    @31
    @6
    @19
    @11
    @24
    @12
    @25
    @31
    @0
    cM
    chash
    @32
    fveq2d
    @31
    vx
    vy
    cvv
    cvv
    @5
    @18
    @31
    @1
    cvv
    wcel
    #
    vy
    cv
    cvv
    wcel
    #
    w3a
    #
    @4
    @17
    @1
    cconcat
    @35
    @3
    @16
    @35
    @1
    @2
    cF
    @29
    @30
    wph
    @33
    @34
    simp1rr
    fveq1d
    s1eqd
    oveq2d
    mpt2eq3dva
    @31
    @10
    @23
    cn0
    @31
    @9
    @22
    @31
    @0
    cM
    @8
    @21
    cconcat
    @32
    @31
    @7
    @20
    @31
    @0
    cM
    @2
    cF
    wph
    @29
    @30
    simprr
    @32
    fveq12d
    s1eqd
    oveq12d
    sneqd
    xpeq2d
    seqeq123d
    coeq2d
    uneq12d
    wph
    cM
    cS
    cword
    #
    wcel
    cM
    cvv
    wcel
    #
    sseqval.2
    cM
    @36
    elex
    syl
    #
    wph
    cW
    cS
    cF
    wf
    cW
    cvv
    wcel
    cF
    cvv
    wcel
    sseqval.4
    wph
    cW
    @36
    chash
    ccnv
    @25
    cuz
    cfv
    cima
    #
    cin
    #
    cvv
    sseqval.3
    wph
    cS
    cvv
    wcel
    @36
    cvv
    wcel
    @40
    cvv
    wcel
    sseqval.1
    cS
    cvv
    wrdexg
    @36
    @39
    cvv
    inex1g
    3syl
    syl5eqel
    cW
    cS
    cvv
    cF
    fex
    syl2anc
    wph
    @37
    @27
    cvv
    wcel
    #
    @28
    cvv
    wcel
    @38
    wph
    clsw
    wfun
    #
    @26
    cvv
    wcel
    #
    @41
    @42
    wph
    vx
    cvv
    @1
    chash
    cfv
    c1
    cmin
    co
    @1
    cfv
    clsw
    vx
    df-lsw
    funmpt2
    a1i
    @43
    wph
    @19
    @24
    @25
    seqex
    a1i
    clsw
    @26
    cvv
    cofunexg
    syl2anc
    cM
    @27
    cvv
    cvv
    unexg
    syl2anc
    ovmpt2d
end
