include "co.mm"
include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "c0g.mm"
include "cif.mm"
include "cmpt.mm"
include "cof.mm"
include "ctsu.mm"
include "wa.mm"
include "ffvelrnda.mm"
include "cmnd.mm"
include "ccmn.mm"
include "cmnmnd.mm"
include "syl.mm"
include "eqid.mm"
include "mndidcl.mm"
include "adantr.mm"
include "ifcld.mm"
include "fmptd.mm"
include "cres.mm"
include "feqmptd.mm"
include "reseq1d.mm"
include "wss.mm"
include "wceq.mm"
include "cun.mm"
include "ssun1.mm"
include "syl5sseqr.mm"
include "iftrue.mm"
include "mpteq2ia.mm"
include "resmpt.mm"
include "3eqtr4a.mm"
include "eqtr4d.mm"
include "oveq2d.mm"
include "ctmd.mm"
include "ctps.mm"
include "tmdtps.mm"
include "cdif.mm"
include "wn.mm"
include "eldifn.mm"
include "adantl.mm"
include "iffalsed.mm"
include "suppss2.mm"
include "tsmsres.mm"
include "eqtrd.mm"
include "eleqtrd.mm"
include "ssun2.mm"
include "tsmsadd.mm"
include "wi.mm"
include "cin.mm"
include "c0.mm"
include "noel.mm"
include "eleq2.mm"
include "mtbiri.mm"
include "elin.mm"
include "sylnib.mm"
include "imnan.mm"
include "sylibr.mm"
include "imp.mm"
include "oveq12d.mm"
include "mndrid.mm"
include "sylan.mm"
include "syldan.mm"
include "con2d.mm"
include "mndlid.mm"
include "wo.mm"
include "eleq2d.mm"
include "elun.mm"
include "syl6bb.mm"
include "biimpa.mm"
include "mpjaodan.mm"
include "mpteq2dva.mm"
include "eqidd.mm"
include "offval2.mm"
include "eleqtrrd.mm"

theorem tsmssplit
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cF: class F
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  let vk: setvar k
  assume tsmssplit.b: |- B = ( Base ` G )
  assume tsmssplit.p: |- .+ = ( +g ` G )
  assume tsmssplit.1: |- ( ph -> G e. CMnd )
  assume tsmssplit.2: |- ( ph -> G e. TopMnd )
  assume tsmssplit.a: |- ( ph -> A e. V )
  assume tsmssplit.f: |- ( ph -> F : A --> B )
  assume tsmssplit.x: |- ( ph -> X e. ( G tsums ( F |` C ) ) )
  assume tsmssplit.y: |- ( ph -> Y e. ( G tsums ( F |` D ) ) )
  assume tsmssplit.i: |- ( ph -> ( C i^i D ) = (/) )
  assume tsmssplit.u: |- ( ph -> A = ( C u. D ) )


  assert |- ( ph -> ( X .+ Y ) e. ( G tsums F ) )

  proof
    wph
    cX
    cY
    c.pl
    co
    cG
    vk
    cA
    vk
    cv
    #
    cC
    wcel
    #
    @0
    cF
    cfv
    #
    cG
    c0g
    cfv
    #
    cif
    #
    cmpt
    #
    vk
    cA
    @0
    cD
    wcel
    #
    @2
    @3
    cif
    #
    cmpt
    #
    c.pl
    cof
    co
    #
    ctsu
    co
    cG
    cF
    ctsu
    co
    wph
    cA
    cB
    c.pl
    @5
    cG
    @8
    cV
    cX
    cY
    tsmssplit.b
    tsmssplit.p
    tsmssplit.1
    tsmssplit.2
    tsmssplit.a
    wph
    vk
    cA
    @4
    cB
    @5
    wph
    @0
    cA
    wcel
    #
    wa
    #
    @1
    @2
    @3
    cB
    wph
    cA
    cB
    @0
    cF
    tsmssplit.f
    ffvelrnda
    #
    wph
    @3
    cB
    wcel
    #
    @10
    wph
    cG
    cmnd
    wcel
    #
    @13
    wph
    cG
    ccmn
    wcel
    @14
    tsmssplit.1
    cG
    cmnmnd
    syl
    #
    cB
    cG
    @3
    tsmssplit.b
    @3
    eqid
    #
    mndidcl
    syl
    adantr
    #
    ifcld
    #
    @5
    eqid
    fmptd
    #
    wph
    vk
    cA
    @7
    cB
    @8
    @11
    @6
    @2
    @3
    cB
    @12
    @17
    ifcld
    #
    @8
    eqid
    fmptd
    #
    wph
    cX
    cG
    cF
    cC
    cres
    #
    ctsu
    co
    #
    cG
    @5
    ctsu
    co
    #
    tsmssplit.x
    wph
    @23
    cG
    @5
    cC
    cres
    #
    ctsu
    co
    @24
    wph
    @22
    @25
    cG
    ctsu
    wph
    @22
    vk
    cA
    @2
    cmpt
    #
    cC
    cres
    #
    @25
    wph
    cF
    @26
    cC
    wph
    vk
    cA
    cB
    cF
    tsmssplit.f
    feqmptd
    #
    reseq1d
    wph
    cC
    cA
    wss
    #
    @25
    @27
    wceq
    wph
    cC
    cD
    cun
    #
    cC
    cA
    cC
    cD
    ssun1
    tsmssplit.u
    syl5sseqr
    @29
    vk
    cC
    @4
    cmpt
    vk
    cC
    @2
    cmpt
    @25
    @27
    vk
    cC
    @4
    @2
    @1
    @2
    @3
    iftrue
    #
    mpteq2ia
    vk
    cA
    cC
    @4
    resmpt
    vk
    cA
    cC
    @2
    resmpt
    3eqtr4a
    syl
    eqtr4d
    oveq2d
    wph
    cA
    cB
    @5
    cG
    cV
    cC
    @3
    tsmssplit.b
    @16
    tsmssplit.1
    wph
    cG
    ctmd
    wcel
    cG
    ctps
    wcel
    tsmssplit.2
    cG
    tmdtps
    syl
    #
    tsmssplit.a
    @19
    wph
    cA
    @4
    vk
    cV
    cC
    @3
    wph
    @0
    cA
    cC
    cdif
    wcel
    #
    wa
    @1
    @2
    @3
    @33
    @1
    wn
    #
    wph
    @0
    cA
    cC
    eldifn
    adantl
    iffalsed
    tsmssplit.a
    suppss2
    tsmsres
    eqtrd
    eleqtrd
    wph
    cY
    cG
    cF
    cD
    cres
    #
    ctsu
    co
    #
    cG
    @8
    ctsu
    co
    #
    tsmssplit.y
    wph
    @36
    cG
    @8
    cD
    cres
    #
    ctsu
    co
    @37
    wph
    @35
    @38
    cG
    ctsu
    wph
    @35
    @26
    cD
    cres
    #
    @38
    wph
    cF
    @26
    cD
    @28
    reseq1d
    wph
    cD
    cA
    wss
    #
    @38
    @39
    wceq
    wph
    @30
    cD
    cA
    cD
    cC
    ssun2
    tsmssplit.u
    syl5sseqr
    @40
    vk
    cD
    @7
    cmpt
    vk
    cD
    @2
    cmpt
    @38
    @39
    vk
    cD
    @7
    @2
    @6
    @2
    @3
    iftrue
    #
    mpteq2ia
    vk
    cA
    cD
    @7
    resmpt
    vk
    cA
    cD
    @2
    resmpt
    3eqtr4a
    syl
    eqtr4d
    oveq2d
    wph
    cA
    cB
    @8
    cG
    cV
    cD
    @3
    tsmssplit.b
    @16
    tsmssplit.1
    @32
    tsmssplit.a
    @21
    wph
    cA
    @7
    vk
    cV
    cD
    @3
    wph
    @0
    cA
    cD
    cdif
    wcel
    #
    wa
    @6
    @2
    @3
    @42
    @6
    wn
    #
    wph
    @0
    cA
    cD
    eldifn
    adantl
    iffalsed
    tsmssplit.a
    suppss2
    tsmsres
    eqtrd
    eleqtrd
    tsmsadd
    wph
    cF
    @9
    cG
    ctsu
    wph
    cF
    vk
    cA
    @4
    @7
    c.pl
    co
    #
    cmpt
    #
    @9
    wph
    cF
    @26
    @45
    @28
    wph
    vk
    cA
    @44
    @2
    @11
    @1
    @44
    @2
    wceq
    @6
    @11
    @1
    wa
    #
    @44
    @2
    @3
    c.pl
    co
    #
    @2
    @46
    @4
    @2
    @7
    @3
    c.pl
    @1
    @4
    @2
    wceq
    @11
    @31
    adantl
    @46
    @6
    @2
    @3
    @11
    @1
    @43
    @11
    @1
    @6
    wa
    #
    wn
    @1
    @43
    wi
    @11
    @0
    cC
    cD
    cin
    #
    wcel
    #
    @48
    wph
    @50
    wn
    #
    @10
    wph
    @49
    c0
    wceq
    #
    @51
    tsmssplit.i
    @52
    @50
    @0
    c0
    wcel
    @0
    noel
    @49
    c0
    @0
    eleq2
    mtbiri
    syl
    adantr
    @0
    cC
    cD
    elin
    sylnib
    @1
    @6
    imnan
    sylibr
    #
    imp
    iffalsed
    oveq12d
    @11
    @47
    @2
    wceq
    #
    @1
    wph
    @10
    @2
    cB
    wcel
    #
    @54
    @12
    wph
    @14
    @55
    @54
    @15
    cB
    c.pl
    cG
    @2
    @3
    tsmssplit.b
    tsmssplit.p
    @16
    mndrid
    sylan
    syldan
    adantr
    eqtrd
    @11
    @6
    wa
    #
    @44
    @3
    @2
    c.pl
    co
    #
    @2
    @56
    @4
    @3
    @7
    @2
    c.pl
    @56
    @1
    @2
    @3
    @11
    @6
    @34
    @11
    @1
    @6
    @53
    con2d
    imp
    iffalsed
    @6
    @7
    @2
    wceq
    @11
    @41
    adantl
    oveq12d
    @11
    @57
    @2
    wceq
    #
    @6
    wph
    @10
    @55
    @58
    @12
    wph
    @14
    @55
    @58
    @15
    cB
    c.pl
    cG
    @2
    @3
    tsmssplit.b
    tsmssplit.p
    @16
    mndlid
    sylan
    syldan
    adantr
    eqtrd
    wph
    @10
    @1
    @6
    wo
    #
    wph
    @10
    @0
    @30
    wcel
    @59
    wph
    cA
    @30
    @0
    tsmssplit.u
    eleq2d
    @0
    cC
    cD
    elun
    syl6bb
    biimpa
    mpjaodan
    mpteq2dva
    eqtr4d
    wph
    vk
    cA
    @4
    @7
    c.pl
    @5
    @8
    cV
    cB
    cB
    tsmssplit.a
    @18
    @20
    wph
    @5
    eqidd
    wph
    @8
    eqidd
    offval2
    eqtr4d
    oveq2d
    eleqtrrd
end
