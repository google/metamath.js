include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cmin.mm"
include "cfv.mm"
include "cmpt2.mm"
include "chash.mm"
include "cc0.mm"
include "clmat.mm"
include "cword.mm"
include "wcel.mm"
include "wceq.mm"
include "lmatval.mm"
include "syl.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "cfzo.mm"
include "cn.mm"
include "lbfzo0.mm"
include "sylibr.mm"
include "wi.mm"
include "cn0.mm"
include "0nn0.mm"
include "a1i.mm"
include "wa.mm"
include "simpr.mm"
include "eleq1d.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "ex.mm"
include "vtocld.mm"
include "mpd.mm"
include "eqidd.mm"
include "mpt2eq123dv.mm"
include "eqtrd.mm"
include "fzfid.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "fz1fzo0m1.mm"
include "eleqtrrd.mm"
include "wrdsymbcl.mm"
include "syl2anc.mm"
include "simp3.mm"
include "cvv.mm"
include "ovexd.mm"
include "eleq12d.mm"
include "imp.mm"
include "sylan2.mm"
include "3adant3.mm"
include "matbas2d.mm"
include "eqeltrd.mm"

theorem lmatcl
  let wph: wff ph
  let cP: class P
  let cR: class R
  let vi: setvar i
  let cM: class M
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let vj: setvar j
  let vm: setvar m
  let cI: class I
  let cJ: class J
  let vk: setvar k
  assume lmatfval.m: |- M = ( litMat ` W )
  assume lmatfval.n: |- ( ph -> N e. NN )
  assume lmatfval.w: |- ( ph -> W e. Word Word V )
  assume lmatfval.1: |- ( ph -> ( # ` W ) = N )
  assume lmatfval.2: |- ( ( ph /\ i e. ( 0 ..^ N ) ) -> ( # ` ( W ` i ) ) = N )
  assume lmatcl.b: |- V = ( Base ` R )
  assume lmatcl.1: |- O = ( ( 1 ... N ) Mat R )
  assume lmatcl.2: |- P = ( Base ` O )
  assume lmatcl.r: |- ( ph -> R e. X )

  disjoint M i
  disjoint N i
  disjoint W i
  disjoint i ph
  disjoint M j
  disjoint M m
  disjoint i j
  disjoint i m
  disjoint j m
  disjoint I i
  disjoint I j
  disjoint J i
  disjoint J j
  disjoint W j
  disjoint j ph
  disjoint N j
  disjoint N k
  disjoint i k
  disjoint j k
  disjoint V j
  disjoint V k
  disjoint W k
  disjoint k ph
  assert |- ( ph -> M e. P )

  proof
    wph
    cM
    vk
    vj
    c1
    cN
    cfz
    co
    #
    @0
    vj
    cv
    #
    c1
    cmin
    co
    #
    vk
    cv
    #
    c1
    cmin
    co
    #
    cW
    cfv
    #
    cfv
    #
    cmpt2
    #
    cP
    wph
    cM
    vk
    vj
    c1
    cW
    chash
    cfv
    #
    cfz
    co
    #
    c1
    cc0
    cW
    cfv
    #
    chash
    cfv
    #
    cfz
    co
    #
    @6
    cmpt2
    #
    @7
    wph
    cM
    cW
    clmat
    cfv
    #
    @13
    lmatfval.m
    wph
    cW
    cV
    cword
    #
    cword
    #
    wcel
    #
    @14
    @13
    wceq
    lmatfval.w
    vk
    vj
    cW
    @16
    lmatval
    syl
    syl5eq
    wph
    vk
    vj
    @9
    @12
    @6
    @0
    @0
    @6
    wph
    @8
    cN
    c1
    cfz
    lmatfval.1
    oveq2d
    wph
    @11
    cN
    c1
    cfz
    wph
    cc0
    cc0
    cN
    cfzo
    co
    #
    wcel
    #
    @11
    cN
    wceq
    #
    wph
    cN
    cn
    wcel
    @19
    lmatfval.n
    cN
    lbfzo0
    sylibr
    wph
    vi
    cv
    #
    @18
    wcel
    #
    @21
    cW
    cfv
    #
    chash
    cfv
    #
    cN
    wceq
    #
    wi
    #
    @19
    @20
    wi
    vi
    cc0
    cn0
    cc0
    cn0
    wcel
    wph
    0nn0
    a1i
    wph
    @21
    cc0
    wceq
    #
    wa
    #
    @22
    @19
    @25
    @20
    @28
    @21
    cc0
    @18
    wph
    @27
    simpr
    #
    eleq1d
    @28
    @24
    @11
    cN
    @28
    @23
    @10
    chash
    @28
    @21
    cc0
    cW
    @29
    fveq2d
    fveq2d
    eqeq1d
    imbi12d
    wph
    @22
    @25
    lmatfval.2
    ex
    #
    vtocld
    mpd
    oveq2d
    wph
    @6
    eqidd
    mpt2eq123dv
    eqtrd
    wph
    vk
    vj
    cO
    cP
    @6
    cR
    cV
    @0
    cX
    lmatcl.1
    lmatcl.b
    lmatcl.2
    wph
    c1
    cN
    fzfid
    lmatcl.r
    wph
    @3
    @0
    wcel
    #
    @1
    @0
    wcel
    #
    w3a
    #
    @5
    @15
    wcel
    #
    @2
    cc0
    @5
    chash
    cfv
    #
    cfzo
    co
    #
    wcel
    @6
    cV
    wcel
    @33
    @17
    @4
    cc0
    @8
    cfzo
    co
    #
    wcel
    @34
    wph
    @31
    @17
    @32
    lmatfval.w
    3ad2ant1
    @33
    @4
    @18
    @37
    @33
    @31
    @4
    @18
    wcel
    #
    wph
    @31
    @32
    simp2
    @3
    cN
    fz1fzo0m1
    #
    syl
    @33
    @8
    cN
    cc0
    cfzo
    wph
    @31
    @8
    cN
    wceq
    @32
    lmatfval.1
    3ad2ant1
    oveq2d
    eleqtrrd
    @4
    @15
    cW
    wrdsymbcl
    syl2anc
    @33
    @2
    @18
    @36
    @33
    @32
    @2
    @18
    wcel
    wph
    @31
    @32
    simp3
    @1
    cN
    fz1fzo0m1
    syl
    @33
    @35
    cN
    cc0
    cfzo
    wph
    @31
    @35
    cN
    wceq
    #
    @32
    @31
    wph
    @38
    @40
    @39
    wph
    @38
    @40
    wph
    @26
    @38
    @40
    wi
    vi
    @4
    cvv
    wph
    @3
    c1
    cmin
    ovexd
    wph
    @21
    @4
    wceq
    #
    wa
    #
    @22
    @38
    @25
    @40
    @42
    @21
    @4
    @18
    @18
    wph
    @41
    simpr
    #
    @42
    @18
    eqidd
    eleq12d
    @42
    @24
    @35
    cN
    @42
    @23
    @5
    chash
    @42
    @21
    @4
    cW
    @43
    fveq2d
    fveq2d
    eqeq1d
    imbi12d
    @30
    vtocld
    imp
    sylan2
    3adant3
    oveq2d
    eleqtrrd
    @2
    cV
    @5
    wrdsymbcl
    syl2anc
    matbas2d
    eqeltrd
end
