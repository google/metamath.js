include "cmul.mm"
include "cseq.mm"
include "cfv.mm"
include "cvv.mm"
include "cuz.mm"
include "eqid.mm"
include "wcel.mm"
include "cz.mm"
include "eluzelz.mm"
include "syl.mm"
include "seqex.mm"
include "a1i.mm"
include "cc.mm"
include "eluzel2.mm"
include "cv.mm"
include "wa.mm"
include "c1.mm"
include "cif.mm"
include "wceq.mm"
include "adantl.mm"
include "iftrue.mm"
include "adantlr.mm"
include "eqeltrd.mm"
include "ex.mm"
include "wn.mm"
include "iffalse.mm"
include "ax-1cn.mm"
include "syl6eqel.mm"
include "pm2.61d1.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "prodf.mm"
include "ffvelrnd.mm"
include "co.mm"
include "mulid1.mm"
include "adantr.mm"
include "simpr.mm"
include "caddc.mm"
include "cfz.mm"
include "elfzuz.mm"
include "cdif.mm"
include "sseld.mm"
include "fznuz.mm"
include "syl6.mm"
include "con2d.mm"
include "imp.mm"
include "eldifd.mm"
include "weq.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "eldifi.mm"
include "eldifn.mm"
include "eqtrd.mm"
include "vtoclga.mm"
include "sylan2.mm"
include "seqid2.mm"
include "eqcomd.mm"
include "climconst.mm"

theorem fprodcvg
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let vm: setvar m
  let vn: setvar n
  assume prodmo.1: |- F = ( k e. ZZ |-> if ( k e. A , B , 1 ) )
  assume prodmo.2: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume prodrb.3: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume fprodcvg.4: |- ( ph -> A C_ ( M ... N ) )

  disjoint M k
  disjoint N k
  disjoint A k
  disjoint F k
  disjoint k ph
  disjoint F m
  disjoint M m
  disjoint k m
  disjoint m ph
  disjoint N m
  disjoint m n
  disjoint A n
  disjoint k n
  disjoint F n
  disjoint n ph
  disjoint M n
  disjoint N n
  assert |- ( ph -> seq M ( x. , F ) ~~> ( seq M ( x. , F ) ` N ) )

  proof
    wph
    cN
    cmul
    cF
    cM
    cseq
    #
    cfv
    #
    vn
    @0
    cN
    cvv
    cN
    cuz
    cfv
    #
    @2
    eqid
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    cN
    cz
    wcel
    prodrb.3
    cM
    cN
    eluzelz
    syl
    @0
    cvv
    wcel
    wph
    cmul
    cF
    cM
    seqex
    a1i
    wph
    @3
    cc
    cN
    @0
    wph
    vk
    cF
    cM
    @3
    @3
    eqid
    #
    wph
    @4
    cM
    cz
    wcel
    #
    prodrb.3
    cM
    cN
    eluzel2
    syl
    #
    wph
    vk
    cv
    #
    @3
    wcel
    #
    wa
    #
    @8
    cF
    cfv
    #
    @8
    cA
    wcel
    #
    cB
    c1
    cif
    #
    cc
    @10
    @8
    cz
    wcel
    #
    @13
    cc
    wcel
    #
    @11
    @13
    wceq
    #
    @9
    @14
    wph
    cM
    @8
    eluzelz
    adantl
    @10
    @12
    @15
    @10
    @12
    @15
    @10
    @12
    wa
    @13
    cB
    cc
    @12
    @13
    cB
    wceq
    @10
    @12
    cB
    c1
    iftrue
    adantl
    wph
    @12
    cB
    cc
    wcel
    @9
    prodmo.2
    adantlr
    eqeltrd
    ex
    @12
    wn
    #
    @13
    c1
    cc
    @12
    cB
    c1
    iffalse
    #
    ax-1cn
    syl6eqel
    pm2.61d1
    #
    vk
    cz
    @13
    cc
    cF
    prodmo.1
    fvmpt2
    #
    syl2anc
    @19
    eqeltrd
    #
    prodf
    prodrb.3
    ffvelrnd
    wph
    vn
    cv
    #
    @2
    wcel
    #
    wa
    #
    @1
    @22
    @0
    cfv
    @24
    vm
    cmul
    cc
    cF
    cN
    cM
    @22
    c1
    vm
    cv
    #
    cc
    wcel
    @25
    c1
    cmul
    co
    @25
    wceq
    @24
    @25
    mulid1
    adantl
    wph
    @4
    @23
    prodrb.3
    adantr
    #
    wph
    @23
    simpr
    @24
    @3
    cc
    cN
    @0
    @24
    vk
    cF
    cM
    @3
    @5
    wph
    @6
    @23
    @7
    adantr
    wph
    @9
    @11
    cc
    wcel
    @23
    @21
    adantlr
    prodf
    @26
    ffvelrnd
    wph
    @25
    cN
    c1
    caddc
    co
    #
    @22
    cfz
    co
    wcel
    #
    @25
    cF
    cfv
    #
    c1
    wceq
    #
    @23
    @28
    wph
    @25
    @27
    cuz
    cfv
    wcel
    #
    @30
    @25
    @27
    @22
    elfzuz
    wph
    @31
    wa
    #
    @25
    cz
    cA
    cdif
    #
    wcel
    @30
    @32
    @25
    cz
    cA
    @31
    @25
    cz
    wcel
    wph
    @27
    @25
    eluzelz
    adantl
    wph
    @31
    @25
    cA
    wcel
    #
    wn
    wph
    @34
    @31
    wph
    @34
    @25
    cM
    cN
    cfz
    co
    #
    wcel
    @31
    wn
    wph
    cA
    @35
    @25
    fprodcvg.4
    sseld
    @25
    cM
    cN
    fznuz
    syl6
    con2d
    imp
    eldifd
    @11
    c1
    wceq
    @30
    vk
    @25
    @33
    vk
    vm
    weq
    @11
    @29
    c1
    @8
    @25
    cF
    fveq2
    eqeq1d
    @8
    @33
    wcel
    #
    @11
    @13
    c1
    @36
    @14
    @15
    @16
    @8
    cz
    cA
    eldifi
    @36
    @13
    c1
    cc
    @36
    @17
    @13
    c1
    wceq
    @8
    cz
    cA
    eldifn
    @18
    syl
    #
    ax-1cn
    syl6eqel
    @20
    syl2anc
    @37
    eqtrd
    vtoclga
    syl
    sylan2
    adantlr
    seqid2
    eqcomd
    climconst
end
