include "cv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cexp.mm"
include "cfz.mm"
include "cprod.mm"
include "cmul.mm"
include "cmpt.mm"
include "cc0.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cif.mm"
include "caddc.mm"
include "cvv.mm"
include "simpr.mm"
include "cc.mm"
include "wss.mm"
include "cnex.mm"
include "ssex.mm"
include "mptexg.mm"
include "3syl.mm"
include "adantr.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "ovexd.mm"
include "fvmpt2d.mm"
include "an32s.mm"
include "prodeq2dv.mm"
include "cuz.mm"
include "cn0.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "sselda.mm"
include "elfzelz.mm"
include "zcnd.mm"
include "adantl.mm"
include "subcld.mm"
include "cn.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "nnnn0d.mm"
include "ifcld.mm"
include "ad2antrr.mm"
include "expcld.mm"
include "oveq2.mm"
include "iftrue.mm"
include "oveq12d.mm"
include "fprod1p.mm"
include "subid1d.mm"
include "oveq1d.mm"
include "0p1e1.mm"
include "oveq1i.mm"
include "a1i.mm"
include "0red.mm"
include "1red.mm"
include "zred.mm"
include "clt.mm"
include "wbr.mm"
include "0lt1.mm"
include "elfzle1.mm"
include "ltletrd.mm"
include "gt0ne0d.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "oveq2d.mm"
include "prodeq12rdv.mm"
include "3eqtrrd.mm"
include "mpteq2dva.mm"
include "3eqtr4g.mm"

theorem etransclem4
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cP: class P
  let vj: setvar j
  let cE: class E
  let cF: class F
  let cH: class H
  let cM: class M
  let vk: setvar k
  assume etransclem4.a: |- ( ph -> A C_ CC )
  assume etransclem4.p: |- ( ph -> P e. NN )
  assume etransclem4.M: |- ( ph -> M e. NN0 )
  assume etransclem4.f: |- F = ( x e. A |-> ( ( x ^ ( P - 1 ) ) x. prod_ j e. ( 1 ... M ) ( ( x - j ) ^ P ) ) )
  assume etransclem4.h: |- H = ( j e. ( 0 ... M ) |-> ( x e. A |-> ( ( x - j ) ^ if ( j = 0 , ( P - 1 ) , P ) ) ) )
  assume etransclem4.e: |- E = ( x e. A |-> prod_ j e. ( 0 ... M ) ( ( H ` j ) ` x ) )

  disjoint A j
  disjoint A x
  disjoint j x
  disjoint M j
  disjoint P j
  disjoint j ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> F = E )

  proof
    wph
    vx
    cA
    vx
    cv
    #
    cP
    c1
    cmin
    co
    #
    cexp
    co
    #
    c1
    cM
    cfz
    co
    #
    @0
    vj
    cv
    #
    cmin
    co
    #
    cP
    cexp
    co
    #
    vj
    cprod
    #
    cmul
    co
    #
    cmpt
    vx
    cA
    cc0
    cM
    cfz
    co
    #
    @0
    @4
    cH
    cfv
    #
    cfv
    #
    vj
    cprod
    #
    cmpt
    cF
    cE
    wph
    vx
    cA
    @8
    @12
    wph
    @0
    cA
    wcel
    #
    wa
    #
    @12
    @9
    @5
    @4
    cc0
    wceq
    #
    @1
    cP
    cif
    #
    cexp
    co
    #
    vj
    cprod
    @0
    cc0
    cmin
    co
    #
    @1
    cexp
    co
    #
    cc0
    c1
    caddc
    co
    #
    cM
    cfz
    co
    #
    @17
    vj
    cprod
    #
    cmul
    co
    @8
    @14
    @9
    @11
    @17
    vj
    wph
    @4
    @9
    wcel
    #
    @13
    @11
    @17
    wceq
    wph
    @23
    wa
    #
    vx
    cA
    @17
    @10
    cvv
    @24
    @23
    vx
    cA
    @17
    cmpt
    #
    cvv
    wcel
    #
    @10
    @25
    wceq
    wph
    @23
    simpr
    wph
    @26
    @23
    wph
    cA
    cc
    wss
    cA
    cvv
    wcel
    @26
    etransclem4.a
    cA
    cc
    cnex
    ssex
    vx
    cA
    @17
    cvv
    mptexg
    3syl
    adantr
    vj
    @9
    @25
    cvv
    cH
    etransclem4.h
    fvmpt2
    syl2anc
    @24
    @13
    wa
    @5
    @16
    cexp
    ovexd
    fvmpt2d
    an32s
    prodeq2dv
    @14
    @17
    @19
    vj
    cc0
    cM
    wph
    cM
    cc0
    cuz
    cfv
    #
    wcel
    @13
    wph
    cM
    cn0
    @27
    etransclem4.M
    nn0uz
    syl6eleq
    adantr
    @14
    @23
    wa
    #
    @5
    @16
    @28
    @0
    @4
    @14
    @0
    cc
    wcel
    @23
    wph
    cA
    cc
    @0
    etransclem4.a
    sselda
    #
    adantr
    @23
    @4
    cc
    wcel
    @14
    @23
    @4
    @4
    cc0
    cM
    elfzelz
    zcnd
    adantl
    subcld
    wph
    @16
    cn0
    wcel
    @13
    @23
    wph
    @15
    @1
    cP
    cn0
    wph
    cP
    cn
    wcel
    @1
    cn0
    wcel
    etransclem4.p
    cP
    nnm1nn0
    syl
    wph
    cP
    etransclem4.p
    nnnn0d
    ifcld
    ad2antrr
    expcld
    @15
    @5
    @18
    @16
    @1
    cexp
    @4
    cc0
    @0
    cmin
    oveq2
    @15
    @1
    cP
    iftrue
    oveq12d
    fprod1p
    @14
    @19
    @2
    @22
    @7
    cmul
    @14
    @18
    @0
    @1
    cexp
    @14
    @0
    @29
    subid1d
    oveq1d
    wph
    @22
    @7
    wceq
    @13
    wph
    @21
    @3
    @17
    @6
    vj
    @21
    @3
    wceq
    wph
    @20
    c1
    cM
    cfz
    0p1e1
    oveq1i
    a1i
    @4
    @3
    wcel
    #
    @17
    @6
    wceq
    wph
    @30
    @16
    cP
    @5
    cexp
    @30
    @15
    @1
    cP
    @30
    @4
    cc0
    @30
    @4
    @30
    cc0
    c1
    @4
    @30
    0red
    @30
    1red
    @30
    @4
    @4
    c1
    cM
    elfzelz
    zred
    cc0
    c1
    clt
    wbr
    @30
    0lt1
    a1i
    @4
    c1
    cM
    elfzle1
    ltletrd
    gt0ne0d
    neneqd
    iffalsed
    oveq2d
    adantl
    prodeq12rdv
    adantr
    oveq12d
    3eqtrrd
    mpteq2dva
    etransclem4.f
    etransclem4.e
    3eqtr4g
end
