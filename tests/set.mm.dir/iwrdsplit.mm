include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfzo.mm"
include "cres.mm"
include "chash.mm"
include "cfv.mm"
include "cmin.mm"
include "cop.mm"
include "csubstr.mm"
include "clsw.mm"
include "cs1.mm"
include "cconcat.mm"
include "cword.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "cn0.mm"
include "1nn0.mm"
include "a1i.mm"
include "nn0addcld.mm"
include "subiwrd.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "1re.mm"
include "nn0addge2.mm"
include "sylancr.mm"
include "subiwrdlen.mm"
include "breqtrrd.mm"
include "wb.mm"
include "wrdlenge1n0.mm"
include "syl.mm"
include "mpbird.mm"
include "swrdccatwrd.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "nn0cnd.mm"
include "1cnd.mm"
include "pncand.mm"
include "eqtrd.mm"
include "opeq2d.mm"
include "oveq2d.mm"
include "cfz.mm"
include "nn0fz0.mm"
include "sylib.mm"
include "wa.mm"
include "elfz0add.mm"
include "imp.mm"
include "syl21anc.mm"
include "eleqtrrd.mm"
include "swrd0val.mm"
include "wss.mm"
include "fzossfzop1.mm"
include "resabs1.mm"
include "3syl.mm"
include "3eqtrd.mm"
include "lsw.mm"
include "fveq2d.mm"
include "fzonn0p1.mm"
include "fvres.mm"
include "s1eqd.mm"
include "oveq12d.mm"
include "eqtr3d.mm"

theorem iwrdsplit
  let wph: wff ph
  let cS: class S
  let cF: class F
  let cN: class N
  assume iwrdsplit.s: |- ( ph -> S e. _V )
  assume iwrdsplit.f: |- ( ph -> F : NN0 --> S )
  assume iwrdsplit.n: |- ( ph -> N e. NN0 )


  assert |- ( ph -> ( F |` ( 0 ..^ ( N + 1 ) ) ) = ( ( F |` ( 0 ..^ N ) ) ++ <" ( F ` N ) "> ) )

  proof
    wph
    cF
    cc0
    cN
    c1
    caddc
    co
    #
    cfzo
    co
    #
    cres
    #
    cc0
    @2
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cop
    #
    csubstr
    co
    #
    @2
    clsw
    cfv
    #
    cs1
    #
    cconcat
    co
    #
    @2
    cF
    cc0
    cN
    cfzo
    co
    #
    cres
    #
    cN
    cF
    cfv
    #
    cs1
    #
    cconcat
    co
    wph
    @2
    cS
    cword
    #
    wcel
    #
    @2
    c0
    wne
    #
    @9
    @2
    wceq
    wph
    cS
    cF
    @0
    iwrdsplit.s
    iwrdsplit.f
    wph
    cN
    c1
    iwrdsplit.n
    c1
    cn0
    wcel
    #
    wph
    1nn0
    a1i
    #
    nn0addcld
    #
    subiwrd
    #
    wph
    @16
    c1
    @3
    cle
    wbr
    #
    wph
    c1
    @0
    @3
    cle
    wph
    c1
    cr
    wcel
    cN
    cn0
    wcel
    #
    c1
    @0
    cle
    wbr
    1re
    iwrdsplit.n
    c1
    cN
    nn0addge2
    sylancr
    wph
    cS
    cF
    @0
    iwrdsplit.s
    iwrdsplit.f
    @19
    subiwrdlen
    #
    breqtrrd
    wph
    @15
    @16
    @21
    wb
    @20
    cS
    @2
    wrdlenge1n0
    syl
    mpbird
    cS
    @2
    swrdccatwrd
    syl2anc
    wph
    @6
    @11
    @8
    @13
    cconcat
    wph
    @6
    @2
    cc0
    cN
    cop
    #
    csubstr
    co
    #
    @2
    @10
    cres
    #
    @11
    wph
    @5
    @24
    @2
    csubstr
    wph
    @4
    cN
    cc0
    wph
    @4
    @0
    c1
    cmin
    co
    cN
    wph
    @3
    @0
    c1
    cmin
    @23
    oveq1d
    wph
    cN
    c1
    wph
    cN
    iwrdsplit.n
    nn0cnd
    wph
    1cnd
    pncand
    eqtrd
    #
    opeq2d
    oveq2d
    wph
    @15
    cN
    cc0
    @3
    cfz
    co
    #
    wcel
    @25
    @26
    wceq
    @20
    wph
    cN
    cc0
    @0
    cfz
    co
    #
    @28
    wph
    @22
    @17
    cN
    cc0
    cN
    cfz
    co
    wcel
    #
    cN
    @29
    wcel
    #
    iwrdsplit.n
    @18
    wph
    @22
    @30
    iwrdsplit.n
    cN
    nn0fz0
    sylib
    @22
    @17
    wa
    @30
    @31
    cN
    c1
    cN
    elfz0add
    imp
    syl21anc
    wph
    @3
    @0
    cc0
    cfz
    @23
    oveq2d
    eleqtrrd
    cS
    @2
    cN
    swrd0val
    syl2anc
    wph
    @22
    @10
    @1
    wss
    @26
    @11
    wceq
    iwrdsplit.n
    cN
    fzossfzop1
    cF
    @10
    @1
    resabs1
    3syl
    3eqtrd
    wph
    @7
    @12
    wph
    @7
    @4
    @2
    cfv
    #
    cN
    @2
    cfv
    #
    @12
    wph
    @15
    @7
    @32
    wceq
    @20
    @2
    @14
    lsw
    syl
    wph
    @4
    cN
    @2
    @27
    fveq2d
    wph
    @22
    cN
    @1
    wcel
    @33
    @12
    wceq
    iwrdsplit.n
    cN
    fzonn0p1
    cN
    @1
    cF
    fvres
    3syl
    3eqtrd
    s1eqd
    oveq12d
    eqtr3d
end
