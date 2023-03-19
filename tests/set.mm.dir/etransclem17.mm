include "cfv.mm"
include "cdvn.mm"
include "co.mm"
include "cv.mm"
include "cneg.mm"
include "caddc.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "cmin.mm"
include "cif.mm"
include "cexp.mm"
include "cmpt.mm"
include "clt.mm"
include "wbr.mm"
include "cfa.mm"
include "cdiv.mm"
include "cmul.mm"
include "cfz.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "dvdmsscn.mm"
include "sselda.mm"
include "adantlr.mm"
include "elfzelz.mm"
include "zcnd.mm"
include "ad2antlr.mm"
include "negsubd.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "mpteq2dva.mm"
include "syl5eq.mm"
include "negeq.mm"
include "oveq2d.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "oveq12d.mm"
include "mpteq2dv.mm"
include "adantl.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "mptexg.mm"
include "syl.mm"
include "fvmptd.mm"
include "fveq1d.mm"
include "cn0.mm"
include "negcld.mm"
include "cn.mm"
include "nnm1nn0.mm"
include "nnnn0d.mm"
include "ifcld.mm"
include "eqid.mm"
include "dvnxpaek.mm"
include "mpdan.mm"
include "adantr.mm"
include "ifeq2d.mm"
include "3eqtrd.mm"

theorem etransclem17
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cS: class S
  let vj: setvar j
  let cH: class H
  let cJ: class J
  let cM: class M
  let cN: class N
  let cX: class X
  let vk: setvar k
  assume etransclem17.s: |- ( ph -> S e. { RR , CC } )
  assume etransclem17.x: |- ( ph -> X e. ( ( TopOpen ` CCfld ) |`t S ) )
  assume etransclem17.p: |- ( ph -> P e. NN )
  assume etransclem17.1: |- H = ( j e. ( 0 ... M ) |-> ( x e. X |-> ( ( x - j ) ^ if ( j = 0 , ( P - 1 ) , P ) ) ) )
  assume etransclem17.J: |- ( ph -> J e. ( 0 ... M ) )
  assume etransclem17.n: |- ( ph -> N e. NN0 )

  disjoint J j
  disjoint J x
  disjoint j x
  disjoint M j
  disjoint M x
  disjoint N x
  disjoint P j
  disjoint P x
  disjoint S x
  disjoint X j
  disjoint X x
  disjoint j ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( ( S Dn ( H ` J ) ) ` N ) = ( x e. X |-> if ( if ( J = 0 , ( P - 1 ) , P ) < N , 0 , ( ( ( ! ` if ( J = 0 , ( P - 1 ) , P ) ) / ( ! ` ( if ( J = 0 , ( P - 1 ) , P ) - N ) ) ) x. ( ( x - J ) ^ ( if ( J = 0 , ( P - 1 ) , P ) - N ) ) ) ) ) )

  proof
    wph
    cN
    cS
    cJ
    cH
    cfv
    #
    cdvn
    co
    #
    cfv
    cN
    cS
    vx
    cX
    vx
    cv
    #
    cJ
    cneg
    #
    caddc
    co
    #
    cJ
    cc0
    wceq
    #
    cP
    c1
    cmin
    co
    #
    cP
    cif
    #
    cexp
    co
    #
    cmpt
    #
    cdvn
    co
    #
    cfv
    #
    vx
    cX
    @7
    cN
    clt
    wbr
    #
    cc0
    @7
    cfa
    cfv
    @7
    cN
    cmin
    co
    #
    cfa
    cfv
    cdiv
    co
    #
    @4
    @13
    cexp
    co
    #
    cmul
    co
    #
    cif
    #
    cmpt
    #
    vx
    cX
    @12
    cc0
    @14
    @2
    cJ
    cmin
    co
    #
    @13
    cexp
    co
    #
    cmul
    co
    #
    cif
    #
    cmpt
    wph
    cN
    @1
    @10
    wph
    @0
    @9
    cS
    cdvn
    wph
    vj
    cJ
    vx
    cX
    @2
    vj
    cv
    #
    cneg
    #
    caddc
    co
    #
    @23
    cc0
    wceq
    #
    @6
    cP
    cif
    #
    cexp
    co
    #
    cmpt
    #
    @9
    cc0
    cM
    cfz
    co
    #
    cH
    cvv
    wph
    cH
    vj
    @30
    vx
    cX
    @2
    @23
    cmin
    co
    #
    @27
    cexp
    co
    #
    cmpt
    #
    cmpt
    vj
    @30
    @29
    cmpt
    etransclem17.1
    wph
    vj
    @30
    @33
    @29
    wph
    @23
    @30
    wcel
    #
    wa
    #
    vx
    cX
    @32
    @28
    @35
    @2
    cX
    wcel
    #
    wa
    #
    @31
    @25
    @27
    cexp
    @37
    @25
    @31
    @37
    @2
    @23
    wph
    @36
    @2
    cc
    wcel
    @34
    wph
    cX
    cc
    @2
    wph
    cS
    cX
    etransclem17.s
    etransclem17.x
    dvdmsscn
    sselda
    #
    adantlr
    @34
    @23
    cc
    wcel
    wph
    @36
    @34
    @23
    @23
    cc0
    cM
    elfzelz
    zcnd
    ad2antlr
    negsubd
    eqcomd
    oveq1d
    mpteq2dva
    mpteq2dva
    syl5eq
    @23
    cJ
    wceq
    #
    @29
    @9
    wceq
    wph
    @39
    vx
    cX
    @28
    @8
    @39
    @25
    @4
    @27
    @7
    cexp
    @39
    @24
    @3
    @2
    caddc
    @23
    cJ
    negeq
    oveq2d
    @39
    @26
    @5
    @6
    cP
    @23
    cJ
    cc0
    eqeq1
    ifbid
    oveq12d
    mpteq2dv
    adantl
    etransclem17.J
    wph
    cX
    ccnfld
    ctopn
    cfv
    cS
    crest
    co
    #
    wcel
    @9
    cvv
    wcel
    etransclem17.x
    vx
    cX
    @8
    @40
    mptexg
    syl
    fvmptd
    oveq2d
    fveq1d
    wph
    cN
    cn0
    wcel
    @11
    @18
    wceq
    etransclem17.n
    wph
    vx
    @3
    cS
    @9
    @7
    cN
    cX
    etransclem17.s
    etransclem17.x
    wph
    cJ
    wph
    cJ
    @30
    wcel
    #
    cJ
    cc
    wcel
    #
    etransclem17.J
    @41
    cJ
    cJ
    cc0
    cM
    elfzelz
    zcnd
    syl
    #
    negcld
    wph
    @5
    @6
    cP
    cn0
    wph
    cP
    cn
    wcel
    @6
    cn0
    wcel
    etransclem17.p
    cP
    nnm1nn0
    syl
    wph
    cP
    etransclem17.p
    nnnn0d
    ifcld
    @9
    eqid
    dvnxpaek
    mpdan
    wph
    vx
    cX
    @17
    @22
    wph
    @36
    wa
    #
    @12
    @16
    @21
    cc0
    @44
    @15
    @20
    @14
    cmul
    @44
    @4
    @19
    @13
    cexp
    @44
    @2
    cJ
    @38
    wph
    @42
    @36
    @43
    adantr
    negsubd
    oveq1d
    oveq2d
    ifeq2d
    mpteq2dva
    3eqtrd
end
