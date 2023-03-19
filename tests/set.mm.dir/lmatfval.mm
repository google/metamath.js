include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cc0.mm"
include "cv.mm"
include "cmin.mm"
include "clmat.mm"
include "cmpt2.mm"
include "cword.mm"
include "wcel.mm"
include "wceq.mm"
include "lmatval.mm"
include "syl.mm"
include "syl5eq.mm"
include "wa.mm"
include "simprl.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "simprr.mm"
include "fveq12d.mm"
include "oveq2d.mm"
include "eleqtrrd.mm"
include "cfzo.mm"
include "1m1e0.mm"
include "cuz.mm"
include "cn.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "eluzfz1.mm"
include "fz1fzo0m1.mm"
include "syl5eqelr.mm"
include "wi.mm"
include "simpr.mm"
include "eleq1d.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "ex.mm"
include "vtocld.mm"
include "mpd.mm"
include "wrdsymbcl.mm"
include "syl2anc.mm"
include "ovmpt2d.mm"

theorem lmatfval
  let wph: wff ph
  let vi: setvar i
  let cI: class I
  let cJ: class J
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let vj: setvar j
  let vm: setvar m
  assume lmatfval.m: |- M = ( litMat ` W )
  assume lmatfval.n: |- ( ph -> N e. NN )
  assume lmatfval.w: |- ( ph -> W e. Word Word V )
  assume lmatfval.1: |- ( ph -> ( # ` W ) = N )
  assume lmatfval.2: |- ( ( ph /\ i e. ( 0 ..^ N ) ) -> ( # ` ( W ` i ) ) = N )
  assume lmatfval.i: |- ( ph -> I e. ( 1 ... N ) )
  assume lmatfval.j: |- ( ph -> J e. ( 1 ... N ) )

  disjoint M i
  disjoint I i
  disjoint J i
  disjoint N i
  disjoint W i
  disjoint i ph
  disjoint M j
  disjoint M m
  disjoint i j
  disjoint i m
  disjoint j m
  disjoint I j
  disjoint J j
  disjoint W j
  disjoint j ph
  assert |- ( ph -> ( I M J ) = ( ( W ` ( I - 1 ) ) ` ( J - 1 ) ) )

  proof
    wph
    vi
    vj
    cI
    cJ
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
    vj
    cv
    #
    c1
    cmin
    co
    #
    vi
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
    cJ
    c1
    cmin
    co
    #
    cI
    c1
    cmin
    co
    #
    cW
    cfv
    #
    cfv
    #
    cM
    cV
    wph
    cM
    cW
    clmat
    cfv
    #
    vi
    vj
    @1
    @4
    @10
    cmpt2
    #
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
    @15
    @16
    wceq
    lmatfval.w
    vi
    vj
    cW
    @18
    lmatval
    syl
    syl5eq
    wph
    @7
    cI
    wceq
    #
    @5
    cJ
    wceq
    #
    wa
    wa
    #
    @6
    @11
    @9
    @13
    @22
    @8
    @12
    cW
    @22
    @7
    cI
    c1
    cmin
    wph
    @20
    @21
    simprl
    oveq1d
    fveq2d
    @22
    @5
    cJ
    c1
    cmin
    wph
    @20
    @21
    simprr
    oveq1d
    fveq12d
    wph
    cI
    c1
    cN
    cfz
    co
    #
    @1
    lmatfval.i
    wph
    @0
    cN
    c1
    cfz
    lmatfval.1
    oveq2d
    eleqtrrd
    wph
    cJ
    @23
    @4
    lmatfval.j
    wph
    @3
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
    @3
    cN
    wceq
    #
    wph
    cc0
    c1
    c1
    cmin
    co
    #
    @24
    1m1e0
    wph
    c1
    @23
    wcel
    #
    @27
    @24
    wcel
    wph
    cN
    c1
    cuz
    cfv
    #
    wcel
    @28
    wph
    cN
    cn
    @29
    lmatfval.n
    nnuz
    syl6eleq
    c1
    cN
    eluzfz1
    syl
    c1
    cN
    fz1fzo0m1
    syl
    syl5eqelr
    #
    wph
    @7
    @24
    wcel
    #
    @7
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
    @25
    @26
    wi
    vi
    cc0
    @24
    @30
    wph
    @7
    cc0
    wceq
    #
    wa
    #
    @31
    @25
    @34
    @26
    @37
    @7
    cc0
    @24
    wph
    @36
    simpr
    #
    eleq1d
    @37
    @33
    @3
    cN
    @37
    @32
    @2
    chash
    @37
    @7
    cc0
    cW
    @38
    fveq2d
    fveq2d
    eqeq1d
    imbi12d
    wph
    @31
    @34
    lmatfval.2
    ex
    #
    vtocld
    mpd
    oveq2d
    eleqtrrd
    wph
    @13
    @17
    wcel
    #
    @11
    cc0
    @13
    chash
    cfv
    #
    cfzo
    co
    #
    wcel
    @14
    cV
    wcel
    wph
    @19
    @12
    cc0
    @0
    cfzo
    co
    #
    wcel
    @40
    lmatfval.w
    wph
    @12
    @24
    @43
    wph
    cI
    @23
    wcel
    @12
    @24
    wcel
    #
    lmatfval.i
    cI
    cN
    fz1fzo0m1
    syl
    #
    wph
    @0
    cN
    cc0
    cfzo
    lmatfval.1
    oveq2d
    eleqtrrd
    @12
    @17
    cW
    wrdsymbcl
    syl2anc
    wph
    @11
    @24
    @42
    wph
    cJ
    @23
    wcel
    @11
    @24
    wcel
    lmatfval.j
    cJ
    cN
    fz1fzo0m1
    syl
    wph
    @41
    cN
    cc0
    cfzo
    wph
    @44
    @41
    cN
    wceq
    #
    @45
    wph
    @35
    @44
    @46
    wi
    vi
    @12
    @24
    @45
    wph
    @7
    @12
    wceq
    #
    wa
    #
    @31
    @44
    @34
    @46
    @48
    @7
    @12
    @24
    wph
    @47
    simpr
    #
    eleq1d
    @48
    @33
    @41
    cN
    @48
    @32
    @13
    chash
    @48
    @7
    @12
    cW
    @49
    fveq2d
    fveq2d
    eqeq1d
    imbi12d
    @39
    vtocld
    mpd
    oveq2d
    eleqtrrd
    @11
    cV
    @13
    wrdsymbcl
    syl2anc
    ovmpt2d
end
