include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cmin.mm"
include "wceq.mm"
include "c1.mm"
include "cif.mm"
include "cexp.mm"
include "cmpt.mm"
include "cfv.mm"
include "cprod.mm"
include "cvv.mm"
include "eqid.mm"
include "etransclem4.mm"
include "wa.mm"
include "wcel.mm"
include "simpr.mm"
include "cc.mm"
include "wss.mm"
include "cnex.mm"
include "ssex.mm"
include "mptexg.mm"
include "3syl.mm"
include "adantr.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "cbvmptv.mm"
include "mpteq2i.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "adantlr.mm"
include "simpl.mm"
include "eqtrd.mm"
include "syl.mm"
include "adantll.mm"
include "eqeltrd.mm"
include "ovexd.mm"
include "fvmptd.mm"
include "prodeq2dv.mm"
include "prodex.mm"
include "a1i.mm"

theorem etransclem13
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let vj: setvar j
  let cF: class F
  let cM: class M
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let vk: setvar k
  assume etransclem13.x: |- ( ph -> X C_ CC )
  assume etransclem13.p: |- ( ph -> P e. NN )
  assume etransclem13.m: |- ( ph -> M e. NN0 )
  assume etransclem13.f: |- F = ( x e. X |-> ( ( x ^ ( P - 1 ) ) x. prod_ j e. ( 1 ... M ) ( ( x - j ) ^ P ) ) )
  assume etransclem13.y: |- ( ph -> Y e. X )

  disjoint M j
  disjoint M x
  disjoint j x
  disjoint P j
  disjoint P x
  disjoint X j
  disjoint X x
  disjoint Y j
  disjoint Y x
  disjoint j ph
  disjoint ph x
  disjoint M y
  disjoint j y
  disjoint x y
  disjoint P y
  disjoint X y
  disjoint Y y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( F ` Y ) = prod_ j e. ( 0 ... M ) ( ( Y - j ) ^ if ( j = 0 , ( P - 1 ) , P ) ) )

  proof
    wph
    vx
    cY
    cc0
    cM
    cfz
    co
    #
    vx
    cv
    #
    vj
    cv
    #
    vj
    @0
    vx
    cX
    @1
    @2
    cmin
    co
    #
    @2
    cc0
    wceq
    cP
    c1
    cmin
    co
    cP
    cif
    #
    cexp
    co
    #
    cmpt
    #
    cmpt
    #
    cfv
    #
    cfv
    #
    vj
    cprod
    #
    @0
    cY
    @2
    cmin
    co
    #
    @4
    cexp
    co
    #
    vj
    cprod
    #
    cX
    cF
    cvv
    wph
    vx
    cX
    cP
    vj
    vx
    cX
    @10
    cmpt
    #
    cF
    @7
    cM
    etransclem13.x
    etransclem13.p
    etransclem13.m
    etransclem13.f
    @7
    eqid
    @14
    eqid
    etransclem4
    wph
    @1
    cY
    wceq
    #
    wa
    #
    @0
    @9
    @12
    vj
    @16
    @2
    @0
    wcel
    #
    wa
    #
    vy
    @1
    vy
    cv
    #
    @2
    cmin
    co
    #
    @4
    cexp
    co
    #
    @12
    cX
    @8
    cvv
    wph
    @17
    @8
    vy
    cX
    @21
    cmpt
    #
    wceq
    #
    @15
    wph
    @17
    wa
    @17
    @22
    cvv
    wcel
    #
    @23
    wph
    @17
    simpr
    wph
    @24
    @17
    wph
    cX
    cc
    wss
    cX
    cvv
    wcel
    @24
    etransclem13.x
    cX
    cc
    cnex
    ssex
    vy
    cX
    @21
    cvv
    mptexg
    3syl
    adantr
    vj
    @0
    @22
    cvv
    @7
    vj
    @0
    @6
    @22
    vx
    vy
    cX
    @5
    @21
    @1
    @19
    wceq
    @3
    @20
    @4
    cexp
    @1
    @19
    @2
    cmin
    oveq1
    oveq1d
    cbvmptv
    mpteq2i
    fvmpt2
    syl2anc
    adantlr
    @16
    @19
    @1
    wceq
    #
    @21
    @12
    wceq
    #
    @17
    @15
    @25
    @26
    wph
    @15
    @25
    wa
    #
    @19
    cY
    wceq
    #
    @26
    @27
    @19
    @1
    cY
    @15
    @25
    simpr
    @15
    @25
    simpl
    eqtrd
    @28
    @20
    @11
    @4
    cexp
    @19
    cY
    @2
    cmin
    oveq1
    oveq1d
    syl
    adantll
    adantlr
    @16
    @1
    cX
    wcel
    @17
    @16
    @1
    cY
    cX
    wph
    @15
    simpr
    wph
    cY
    cX
    wcel
    @15
    etransclem13.y
    adantr
    eqeltrd
    adantr
    @18
    @11
    @4
    cexp
    ovexd
    fvmptd
    prodeq2dv
    etransclem13.y
    @13
    cvv
    wcel
    wph
    @0
    @12
    vj
    prodex
    a1i
    fvmptd
end
