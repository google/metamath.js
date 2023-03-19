include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "cfzo.mm"
include "cv.mm"
include "wcel.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt.mm"
include "cconcat.mm"
include "c1.mm"
include "cmul.mm"
include "csn.mm"
include "cxp.mm"
include "fveq2i.mm"
include "cfn.mm"
include "wceq.mm"
include "fzofi.mm"
include "snfi.mm"
include "hashxp.mm"
include "mp2an.mm"
include "eqtri.mm"
include "cn0.mm"
include "hashfzo0.mm"
include "syl.mm"
include "hashsng.mm"
include "oveq12d.mm"
include "syl5eq.mm"
include "nn0cnd.mm"
include "mulid1d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "wa.mm"
include "simpll.mm"
include "simpr.mm"
include "eleqtrd.mm"
include "wf.mm"
include "fconstg.mm"
include "a1i.mm"
include "feq1d.mm"
include "mpbird.mm"
include "fvconst.mm"
include "sylan.mm"
include "syl2anc.mm"
include "wn.mm"
include "cz.mm"
include "simplr.mm"
include "eqeltrd.mm"
include "nn0zd.mm"
include "fzocatel.mm"
include "syl22anc.mm"
include "ifeqda.mm"
include "mpteq12dva.mm"
include "cvv.mm"
include "ovex.mm"
include "snex.mm"
include "xpex.mm"
include "eqeltri.mm"
include "ccatfval.mm"
include "fconstmpt.mm"
include "3eqtr4g.mm"

theorem ccatmulgnn0dir
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cK: class K
  let cM: class M
  let cN: class N
  let vi: setvar i
  assume ccatmulgnn0dir.a: |- A = ( ( 0 ..^ M ) X. { K } )
  assume ccatmulgnn0dir.b: |- B = ( ( 0 ..^ N ) X. { K } )
  assume ccatmulgnn0dir.c: |- C = ( ( 0 ..^ ( M + N ) ) X. { K } )
  assume ccatmulgnn0dir.k: |- ( ph -> K e. S )
  assume ccatmulgnn0dir.m: |- ( ph -> M e. NN0 )
  assume ccatmulgnn0dir.n: |- ( ph -> N e. NN0 )


  assert |- ( ph -> ( A ++ B ) = C )

  proof
    wph
    vi
    cc0
    cA
    chash
    cfv
    #
    cB
    chash
    cfv
    #
    caddc
    co
    #
    cfzo
    co
    #
    vi
    cv
    #
    cc0
    @0
    cfzo
    co
    #
    wcel
    #
    @4
    cA
    cfv
    #
    @4
    @0
    cmin
    co
    #
    cB
    cfv
    #
    cif
    #
    cmpt
    #
    vi
    cc0
    cM
    cN
    caddc
    co
    #
    cfzo
    co
    #
    cK
    cmpt
    #
    cA
    cB
    cconcat
    co
    #
    cC
    wph
    vi
    @3
    @10
    @13
    cK
    wph
    @2
    @12
    cc0
    cfzo
    wph
    @0
    cM
    @1
    cN
    caddc
    wph
    @0
    cM
    c1
    cmul
    co
    #
    cM
    wph
    @0
    cc0
    cM
    cfzo
    co
    #
    chash
    cfv
    #
    cK
    csn
    #
    chash
    cfv
    #
    cmul
    co
    #
    @16
    @0
    @17
    @19
    cxp
    #
    chash
    cfv
    #
    @21
    cA
    @22
    chash
    ccatmulgnn0dir.a
    fveq2i
    @17
    cfn
    wcel
    @19
    cfn
    wcel
    #
    @23
    @21
    wceq
    cc0
    cM
    fzofi
    cK
    snfi
    #
    @17
    @19
    hashxp
    mp2an
    eqtri
    wph
    @18
    cM
    @20
    c1
    cmul
    wph
    cM
    cn0
    wcel
    @18
    cM
    wceq
    ccatmulgnn0dir.m
    cM
    hashfzo0
    syl
    wph
    cK
    cS
    wcel
    #
    @20
    c1
    wceq
    ccatmulgnn0dir.k
    cK
    cS
    hashsng
    syl
    #
    oveq12d
    syl5eq
    wph
    cM
    wph
    cM
    ccatmulgnn0dir.m
    nn0cnd
    mulid1d
    eqtrd
    #
    wph
    @1
    cN
    c1
    cmul
    co
    #
    cN
    wph
    @1
    cc0
    cN
    cfzo
    co
    #
    chash
    cfv
    #
    @20
    cmul
    co
    #
    @29
    @1
    @30
    @19
    cxp
    #
    chash
    cfv
    #
    @32
    cB
    @33
    chash
    ccatmulgnn0dir.b
    fveq2i
    @30
    cfn
    wcel
    @24
    @34
    @32
    wceq
    cc0
    cN
    fzofi
    @25
    @30
    @19
    hashxp
    mp2an
    eqtri
    wph
    @31
    cN
    @20
    c1
    cmul
    wph
    cN
    cn0
    wcel
    @31
    cN
    wceq
    ccatmulgnn0dir.n
    cN
    hashfzo0
    syl
    @27
    oveq12d
    syl5eq
    wph
    cN
    wph
    cN
    ccatmulgnn0dir.n
    nn0cnd
    mulid1d
    eqtrd
    #
    oveq12d
    oveq2d
    wph
    @4
    @3
    wcel
    #
    wa
    #
    @6
    @7
    @9
    cK
    @37
    @6
    wa
    #
    wph
    @4
    @17
    wcel
    #
    @7
    cK
    wceq
    #
    wph
    @36
    @6
    simpll
    #
    @38
    @4
    @5
    @17
    @37
    @6
    simpr
    @38
    wph
    @5
    @17
    wceq
    @41
    wph
    @0
    cM
    cc0
    cfzo
    @28
    oveq2d
    syl
    eleqtrd
    wph
    @17
    @19
    cA
    wf
    #
    @39
    @40
    wph
    @42
    @17
    @19
    @22
    wf
    #
    wph
    @26
    @43
    ccatmulgnn0dir.k
    @17
    cK
    cS
    fconstg
    syl
    wph
    @17
    @19
    cA
    @22
    cA
    @22
    wceq
    wph
    ccatmulgnn0dir.a
    a1i
    feq1d
    mpbird
    @17
    cK
    @4
    cA
    fvconst
    sylan
    syl2anc
    @37
    @6
    wn
    #
    wa
    #
    wph
    @8
    @30
    wcel
    #
    @9
    cK
    wceq
    #
    wph
    @36
    @44
    simpll
    #
    @45
    @8
    cc0
    @1
    cfzo
    co
    #
    @30
    @45
    @36
    @44
    @0
    cz
    wcel
    @1
    cz
    wcel
    @8
    @49
    wcel
    wph
    @36
    @44
    simplr
    @37
    @44
    simpr
    @45
    @0
    @45
    wph
    @0
    cn0
    wcel
    @48
    wph
    @0
    cM
    cn0
    @28
    ccatmulgnn0dir.m
    eqeltrd
    syl
    nn0zd
    @45
    @1
    @45
    wph
    @1
    cn0
    wcel
    @48
    wph
    @1
    cN
    cn0
    @35
    ccatmulgnn0dir.n
    eqeltrd
    syl
    nn0zd
    @4
    @0
    @1
    fzocatel
    syl22anc
    @45
    wph
    @49
    @30
    wceq
    @48
    wph
    @1
    cN
    cc0
    cfzo
    @35
    oveq2d
    syl
    eleqtrd
    wph
    @30
    @19
    cB
    wf
    #
    @46
    @47
    wph
    @50
    @30
    @19
    @33
    wf
    #
    wph
    @26
    @51
    ccatmulgnn0dir.k
    @30
    cK
    cS
    fconstg
    syl
    wph
    @30
    @19
    cB
    @33
    cB
    @33
    wceq
    wph
    ccatmulgnn0dir.b
    a1i
    feq1d
    mpbird
    @30
    cK
    @8
    cB
    fvconst
    sylan
    syl2anc
    ifeqda
    mpteq12dva
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    @15
    @11
    wceq
    cA
    @22
    cvv
    ccatmulgnn0dir.a
    @17
    @19
    cc0
    cM
    cfzo
    ovex
    cK
    snex
    #
    xpex
    eqeltri
    cB
    @33
    cvv
    ccatmulgnn0dir.b
    @30
    @19
    cc0
    cN
    cfzo
    ovex
    @52
    xpex
    eqeltri
    vi
    cA
    cB
    cvv
    cvv
    ccatfval
    mp2an
    cC
    @13
    @19
    cxp
    @14
    ccatmulgnn0dir.c
    vi
    @13
    cK
    fconstmpt
    eqtri
    3eqtr4g
end
