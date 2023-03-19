include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "ciun.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "simpr.mm"
include "nnred.mm"
include "leidd.mm"
include "cv.mm"
include "wi.mm"
include "caddc.mm"
include "wceq.mm"
include "breq1.mm"
include "oveq2.mm"
include "iuneq1d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "c0.mm"
include "fzo0.mm"
include "iuneq1.mm"
include "ax-mp.mm"
include "0iun.mm"
include "eqtri.mm"
include "0elros.mm"
include "syl.mm"
include "syl5eqel.mm"
include "a1d.mm"
include "csn.mm"
include "cun.mm"
include "simpllr.mm"
include "cuz.mm"
include "cfv.mm"
include "fzosplitsn.mm"
include "nnuz.mm"
include "eleq2s.mm"
include "iunxun.mm"
include "syl6eq.mm"
include "ad3antrrr.mm"
include "clt.mm"
include "wb.mm"
include "nnltp1le.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "ltled.mm"
include "simplr.mm"
include "mpd.mm"
include "csb.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "iunxsngf.mm"
include "simplll.mm"
include "elfzo1.mm"
include "syl3anbrc.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfel.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "chvar.mm"
include "eqeltrd.mm"
include "unelros.mm"
include "syl3anc.mm"
include "ex.mm"
include "nnindd.mm"
include "mpdan.mm"

theorem fiunelros
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cQ: class Q
  let cS: class S
  let vk: setvar k
  let cN: class N
  let cO: class O
  let vs: setvar s
  let vi: setvar i
  let vn: setvar n
  let cA: class A
  let vu: setvar u
  let vv: setvar v
  assume isros.1: |- Q = { s e. ~P ~P O | ( (/) e. s /\ A. x e. s A. y e. s ( ( x u. y ) e. s /\ ( x \ y ) e. s ) ) }
  assume fiunelros.1: |- ( ph -> S e. Q )
  assume fiunelros.2: |- ( ph -> N e. NN )
  assume fiunelros.3: |- ( ( ph /\ k e. ( 1 ..^ N ) ) -> B e. S )

  disjoint N k
  disjoint S k
  disjoint k ph
  disjoint O s
  disjoint S s
  disjoint S x
  disjoint S y
  disjoint s x
  disjoint s y
  disjoint x y
  disjoint B i
  disjoint B n
  disjoint i n
  disjoint N i
  disjoint N n
  disjoint i k
  disjoint k n
  disjoint S i
  disjoint S n
  disjoint i ph
  disjoint n ph
  disjoint A u
  disjoint A v
  disjoint u v
  disjoint B u
  disjoint B v
  disjoint S u
  disjoint S v
  disjoint s u
  disjoint s v
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  assert |- ( ph -> U_ k e. ( 1 ..^ N ) B e. S )

  proof
    wph
    cN
    cn
    wcel
    #
    vk
    c1
    cN
    cfzo
    co
    #
    cB
    ciun
    #
    cS
    wcel
    #
    fiunelros.2
    wph
    @0
    wa
    #
    cN
    cN
    cle
    wbr
    #
    @3
    @4
    cN
    @4
    cN
    wph
    @0
    simpr
    nnred
    leidd
    wph
    vn
    cv
    #
    cN
    cle
    wbr
    #
    vk
    c1
    @6
    cfzo
    co
    #
    cB
    ciun
    #
    cS
    wcel
    #
    wi
    c1
    cN
    cle
    wbr
    #
    vk
    c1
    c1
    cfzo
    co
    #
    cB
    ciun
    #
    cS
    wcel
    #
    wi
    vi
    cv
    #
    cN
    cle
    wbr
    #
    vk
    c1
    @15
    cfzo
    co
    #
    cB
    ciun
    #
    cS
    wcel
    #
    wi
    #
    @15
    c1
    caddc
    co
    #
    cN
    cle
    wbr
    #
    vk
    c1
    @21
    cfzo
    co
    #
    cB
    ciun
    #
    cS
    wcel
    #
    wi
    @5
    @3
    wi
    vn
    vi
    cN
    @6
    c1
    wceq
    #
    @7
    @11
    @10
    @14
    @6
    c1
    cN
    cle
    breq1
    @26
    @9
    @13
    cS
    @26
    vk
    @8
    @12
    cB
    @6
    c1
    c1
    cfzo
    oveq2
    iuneq1d
    eleq1d
    imbi12d
    @6
    @15
    wceq
    #
    @7
    @16
    @10
    @19
    @6
    @15
    cN
    cle
    breq1
    @27
    @9
    @18
    cS
    @27
    vk
    @8
    @17
    cB
    @6
    @15
    c1
    cfzo
    oveq2
    iuneq1d
    eleq1d
    imbi12d
    @6
    @21
    wceq
    #
    @7
    @22
    @10
    @25
    @6
    @21
    cN
    cle
    breq1
    @28
    @9
    @24
    cS
    @28
    vk
    @8
    @23
    cB
    @6
    @21
    c1
    cfzo
    oveq2
    iuneq1d
    eleq1d
    imbi12d
    @6
    cN
    wceq
    #
    @7
    @5
    @10
    @3
    @6
    cN
    cN
    cle
    breq1
    @29
    @9
    @2
    cS
    @29
    vk
    @8
    @1
    cB
    @6
    cN
    c1
    cfzo
    oveq2
    iuneq1d
    eleq1d
    imbi12d
    wph
    @14
    @11
    wph
    @13
    c0
    cS
    @13
    vk
    c0
    cB
    ciun
    #
    c0
    @12
    c0
    wceq
    @13
    @30
    wceq
    c1
    fzo0
    vk
    @12
    c0
    cB
    iuneq1
    ax-mp
    vk
    cB
    0iun
    eqtri
    wph
    cS
    cQ
    wcel
    #
    c0
    cS
    wcel
    fiunelros.1
    vx
    vy
    cQ
    cS
    cO
    vs
    isros.1
    0elros
    syl
    syl5eqel
    a1d
    wph
    @15
    cn
    wcel
    #
    wa
    #
    @20
    wa
    #
    @22
    @25
    @34
    @22
    wa
    #
    @24
    @18
    vk
    @15
    csn
    #
    cB
    ciun
    #
    cun
    #
    cS
    @35
    @24
    vk
    @17
    @36
    cun
    #
    cB
    ciun
    #
    @38
    @35
    @32
    @24
    @40
    wceq
    wph
    @32
    @20
    @22
    simpllr
    #
    @32
    vk
    @23
    @39
    cB
    @23
    @39
    wceq
    @15
    c1
    cuz
    cfv
    cn
    c1
    @15
    fzosplitsn
    nnuz
    eleq2s
    iuneq1d
    syl
    vk
    @17
    @36
    cB
    iunxun
    syl6eq
    @35
    @31
    @19
    @37
    cS
    wcel
    @38
    cS
    wcel
    wph
    @31
    @32
    @20
    @22
    fiunelros.1
    ad3antrrr
    @35
    @16
    @19
    @35
    @15
    cN
    @35
    @15
    @41
    nnred
    @35
    cN
    wph
    @0
    @32
    @20
    @22
    fiunelros.2
    ad3antrrr
    #
    nnred
    @35
    @15
    cN
    clt
    wbr
    #
    @22
    @34
    @22
    simpr
    @35
    @32
    @0
    @43
    @22
    wb
    @41
    @42
    @15
    cN
    nnltp1le
    syl2anc
    mpbird
    #
    ltled
    @33
    @20
    @22
    simplr
    mpd
    @35
    @37
    vk
    @15
    cB
    csb
    #
    cS
    @35
    @32
    @37
    @45
    wceq
    @41
    vk
    @15
    cB
    @45
    cn
    vk
    @15
    cB
    nfcsb1v
    #
    vk
    @15
    cB
    csbeq1a
    #
    iunxsngf
    syl
    @35
    wph
    @15
    @1
    wcel
    #
    @45
    cS
    wcel
    #
    wph
    @32
    @20
    @22
    simplll
    @35
    @32
    @0
    @43
    @48
    @41
    @42
    @44
    cN
    @15
    elfzo1
    syl3anbrc
    wph
    vk
    cv
    #
    @1
    wcel
    #
    wa
    #
    cB
    cS
    wcel
    #
    wi
    wph
    @48
    wa
    #
    @49
    wi
    vk
    vi
    @54
    @49
    vk
    @54
    vk
    nfv
    vk
    @45
    cS
    @46
    vk
    cS
    nfcv
    nfel
    nfim
    @50
    @15
    wceq
    #
    @52
    @54
    @53
    @49
    @55
    @51
    @48
    wph
    @50
    @15
    @1
    eleq1
    anbi2d
    @55
    cB
    @45
    cS
    @47
    eleq1d
    imbi12d
    fiunelros.3
    chvar
    syl2anc
    eqeltrd
    vx
    vy
    @18
    @37
    cQ
    cS
    cO
    vs
    isros.1
    unelros
    syl3anc
    eqeltrd
    ex
    nnindd
    mpd
    mpdan
end
