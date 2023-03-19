include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cneg.mm"
include "cv.mm"
include "cmpt.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "ffvelrnda.mm"
include "renegcld.mm"
include "eqid.mm"
include "fmptd.mm"
include "cdv.mm"
include "co.mm"
include "ccncf.mm"
include "cvv.mm"
include "cc.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "a1i.mm"
include "ax-resscn.mm"
include "sseldi.mm"
include "fvexd.mm"
include "feqmptd.mm"
include "oveq2d.mm"
include "wf.mm"
include "cncff.mm"
include "syl.mm"
include "eqtr3d.mm"
include "dvmptneg.mm"
include "wss.mm"
include "wb.mm"
include "ssid.mm"
include "cncfss.mm"
include "mp2an.mm"
include "negfcncf.mm"
include "cncffvrn.mm"
include "sylancr.mm"
include "mpbird.mm"
include "eqeltrd.mm"
include "cioo.mm"
include "cc0.mm"
include "adantr.mm"
include "cicc.mm"
include "ioossicc.mm"
include "fct2relem.mm"
include "sstrd.mm"
include "sselda.mm"
include "ffvelrnd.mm"
include "lt0neg1d.mm"
include "mpbid.mm"
include "wceq.mm"
include "fveq1d.mm"
include "simpr.mm"
include "fveq2d.mm"
include "negeqd.mm"
include "fvmptd.mm"
include "eqtrd.mm"
include "breqtrrd.mm"
include "fdvposlt.mm"
include "eqidd.mm"
include "3brtr3d.mm"
include "ltnegd.mm"

theorem fdvneggt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let vy: setvar y
  assume fdvposlt.d: |- E = ( C (,) D )
  assume fdvposlt.a: |- ( ph -> A e. E )
  assume fdvposlt.b: |- ( ph -> B e. E )
  assume fdvposlt.f: |- ( ph -> F : E --> RR )
  assume fdvposlt.c: |- ( ph -> ( RR _D F ) e. ( E -cn-> RR ) )
  assume fdvneggt.lt: |- ( ph -> A < B )
  assume fdvneggt.1: |- ( ( ph /\ x e. ( A (,) B ) ) -> ( ( RR _D F ) ` x ) < 0 )

  disjoint A x
  disjoint B x
  disjoint E x
  disjoint F x
  disjoint ph x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint E y
  disjoint F y
  disjoint ph y
  assert |- ( ph -> ( F ` B ) < ( F ` A ) )

  proof
    wph
    cB
    cF
    cfv
    #
    cA
    cF
    cfv
    #
    clt
    wbr
    @1
    cneg
    #
    @0
    cneg
    #
    clt
    wbr
    wph
    cA
    vy
    cE
    vy
    cv
    #
    cF
    cfv
    #
    cneg
    #
    cmpt
    #
    cfv
    cB
    @7
    cfv
    @2
    @3
    clt
    wph
    vx
    cA
    cB
    cC
    cD
    cE
    @7
    fdvposlt.d
    fdvposlt.a
    fdvposlt.b
    wph
    vy
    cE
    @6
    cr
    @7
    wph
    @4
    cE
    wcel
    wa
    #
    @5
    wph
    cE
    cr
    @4
    cF
    fdvposlt.f
    ffvelrnda
    #
    renegcld
    @7
    eqid
    fmptd
    wph
    cr
    @7
    cdv
    co
    #
    vy
    cE
    @4
    cr
    cF
    cdv
    co
    #
    cfv
    #
    cneg
    #
    cmpt
    #
    cE
    cr
    ccncf
    co
    #
    wph
    vy
    @5
    @12
    cr
    cvv
    cE
    cr
    cr
    cc
    cpr
    wcel
    wph
    reelprrecn
    a1i
    @8
    cr
    cc
    @5
    ax-resscn
    @9
    sseldi
    @8
    @4
    @11
    fvexd
    wph
    @11
    cr
    vy
    cE
    @5
    cmpt
    #
    cdv
    co
    vy
    cE
    @12
    cmpt
    wph
    cF
    @16
    cr
    cdv
    wph
    vy
    cE
    cr
    cF
    fdvposlt.f
    feqmptd
    oveq2d
    wph
    vy
    cE
    cr
    @11
    wph
    @11
    @15
    wcel
    cE
    cr
    @11
    wf
    #
    fdvposlt.c
    cE
    cr
    @11
    cncff
    syl
    #
    feqmptd
    eqtr3d
    dvmptneg
    #
    wph
    @14
    @15
    wcel
    #
    cE
    cr
    @14
    wf
    #
    wph
    vy
    cE
    @13
    cr
    @14
    @8
    @12
    wph
    cE
    cr
    @4
    @11
    @18
    ffvelrnda
    renegcld
    @14
    eqid
    #
    fmptd
    wph
    cr
    cc
    wss
    #
    @14
    cE
    cc
    ccncf
    co
    #
    wcel
    #
    @20
    @21
    wb
    ax-resscn
    wph
    @11
    @24
    wcel
    @25
    wph
    @15
    @24
    @11
    @23
    cc
    cc
    wss
    @15
    @24
    wss
    ax-resscn
    cc
    ssid
    cE
    cr
    cc
    cncfss
    mp2an
    fdvposlt.c
    sseldi
    vy
    cE
    @11
    @14
    @22
    negfcncf
    syl
    cE
    cc
    cr
    @14
    cncffvrn
    sylancr
    mpbird
    eqeltrd
    fdvneggt.lt
    wph
    vx
    cv
    #
    cA
    cB
    cioo
    co
    #
    wcel
    #
    wa
    #
    cc0
    @26
    @11
    cfv
    #
    cneg
    #
    @26
    @10
    cfv
    #
    clt
    @29
    @30
    cc0
    clt
    wbr
    cc0
    @31
    clt
    wbr
    fdvneggt.1
    @29
    @30
    @29
    cE
    cr
    @26
    @11
    wph
    @17
    @28
    @18
    adantr
    wph
    @27
    cE
    @26
    wph
    @27
    cA
    cB
    cicc
    co
    #
    cE
    @27
    @33
    wss
    wph
    cA
    cB
    ioossicc
    a1i
    wph
    cA
    cB
    cC
    cD
    cE
    fdvposlt.d
    fdvposlt.a
    fdvposlt.b
    fct2relem
    sstrd
    sselda
    #
    ffvelrnd
    #
    lt0neg1d
    mpbid
    @29
    @32
    @26
    @14
    cfv
    @31
    @29
    @26
    @10
    @14
    wph
    @10
    @14
    wceq
    @28
    @19
    adantr
    fveq1d
    @29
    vy
    @26
    @13
    @31
    cE
    @14
    cr
    @14
    @14
    wceq
    @29
    @22
    a1i
    @29
    @4
    @26
    wceq
    #
    wa
    #
    @12
    @30
    @37
    @4
    @26
    @11
    @29
    @36
    simpr
    fveq2d
    negeqd
    @34
    @29
    @30
    @35
    renegcld
    fvmptd
    eqtrd
    breqtrrd
    fdvposlt
    wph
    vy
    cA
    @6
    @2
    cE
    @7
    cr
    wph
    @7
    eqidd
    #
    wph
    @4
    cA
    wceq
    #
    wa
    #
    @5
    @1
    @40
    @4
    cA
    cF
    wph
    @39
    simpr
    fveq2d
    negeqd
    fdvposlt.a
    wph
    @1
    wph
    cE
    cr
    cA
    cF
    fdvposlt.f
    fdvposlt.a
    ffvelrnd
    #
    renegcld
    fvmptd
    wph
    vy
    cB
    @6
    @3
    cE
    @7
    cr
    @38
    wph
    @4
    cB
    wceq
    #
    wa
    #
    @5
    @0
    @43
    @4
    cB
    cF
    wph
    @42
    simpr
    fveq2d
    negeqd
    fdvposlt.b
    wph
    @0
    wph
    cE
    cr
    cB
    cF
    fdvposlt.f
    fdvposlt.b
    ffvelrnd
    #
    renegcld
    fvmptd
    3brtr3d
    wph
    @0
    @1
    @44
    @41
    ltnegd
    mpbird
end
