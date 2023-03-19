include "cdiv.mm"
include "co.mm"
include "cmpt.mm"
include "cdv.mm"
include "c2.mm"
include "cexp.mm"
include "cneg.mm"
include "cmul.mm"
include "cv.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cr.mm"
include "cpr.mm"
include "wcel.mm"
include "cnelprrecn.mm"
include "a1i.mm"
include "wa.mm"
include "adantr.mm"
include "eldifi.mm"
include "adantl.mm"
include "wne.mm"
include "eldifsni.mm"
include "divcld.mm"
include "sqcld.mm"
include "cz.mm"
include "2z.mm"
include "expne0d.mm"
include "negcld.mm"
include "wceq.mm"
include "dvrec.mm"
include "syl.mm"
include "oveq2.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "negeqd.mm"
include "dvmptco.mm"
include "eldifsn.mm"
include "sylib.mm"
include "simprd.mm"
include "dvmptcl.mm"
include "mulneg1d.mm"
include "div23d.mm"
include "eqcomd.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"

theorem dvrecg
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cV: class V
  let cX: class X
  let vy: setvar y
  assume dvrecg.s: |- ( ph -> S e. { RR , CC } )
  assume dvrecg.a: |- ( ph -> A e. CC )
  assume dvrecg.b: |- ( ( ph /\ x e. X ) -> B e. ( CC \ { 0 } ) )
  assume dvrecg.c: |- ( ( ph /\ x e. X ) -> C e. V )
  assume dvrecg.db: |- ( ph -> ( S _D ( x e. X |-> B ) ) = ( x e. X |-> C ) )

  disjoint A x
  disjoint S x
  disjoint V x
  disjoint X x
  disjoint ph x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint S y
  disjoint ph y
  assert |- ( ph -> ( S _D ( x e. X |-> ( A / B ) ) ) = ( x e. X |-> -u ( ( A x. C ) / ( B ^ 2 ) ) ) )

  proof
    wph
    cS
    vx
    cX
    cA
    cB
    cdiv
    co
    #
    cmpt
    cdv
    co
    vx
    cX
    cA
    cB
    c2
    cexp
    co
    #
    cdiv
    co
    #
    cneg
    #
    cC
    cmul
    co
    #
    cmpt
    vx
    cX
    cA
    cC
    cmul
    co
    @1
    cdiv
    co
    #
    cneg
    #
    cmpt
    wph
    vx
    vy
    cB
    cC
    cA
    vy
    cv
    #
    cdiv
    co
    #
    cA
    @7
    c2
    cexp
    co
    #
    cdiv
    co
    #
    cneg
    #
    cS
    cc
    @0
    @3
    cV
    cc
    cX
    cc
    cc0
    csn
    #
    cdif
    #
    dvrecg.s
    cc
    cr
    cc
    cpr
    wcel
    wph
    cnelprrecn
    a1i
    dvrecg.b
    dvrecg.c
    wph
    @7
    @13
    wcel
    #
    wa
    #
    cA
    @7
    wph
    cA
    cc
    wcel
    #
    @14
    dvrecg.a
    adantr
    #
    @14
    @7
    cc
    wcel
    wph
    @7
    cc
    @12
    eldifi
    adantl
    #
    @14
    @7
    cc0
    wne
    wph
    @7
    cc
    cc0
    eldifsni
    adantl
    #
    divcld
    @15
    @10
    @15
    cA
    @9
    @17
    @15
    @7
    @18
    sqcld
    @15
    @7
    c2
    @18
    @19
    c2
    cz
    wcel
    #
    @15
    2z
    a1i
    expne0d
    divcld
    negcld
    dvrecg.db
    wph
    @16
    cc
    vy
    @13
    @8
    cmpt
    cdv
    co
    vy
    @13
    @11
    cmpt
    wceq
    dvrecg.a
    vy
    cA
    dvrec
    syl
    @7
    cB
    cA
    cdiv
    oveq2
    @7
    cB
    wceq
    #
    @10
    @2
    @21
    @9
    @1
    cA
    cdiv
    @7
    cB
    c2
    cexp
    oveq1
    oveq2d
    negeqd
    dvmptco
    wph
    vx
    cX
    @4
    @6
    wph
    vx
    cv
    cX
    wcel
    #
    wa
    #
    @4
    @2
    cC
    cmul
    co
    #
    cneg
    @6
    @23
    @2
    cC
    @23
    cA
    @1
    wph
    @16
    @22
    dvrecg.a
    adantr
    #
    @23
    cB
    @23
    cB
    @13
    wcel
    #
    cB
    cc
    wcel
    #
    dvrecg.b
    cB
    cc
    @12
    eldifi
    syl
    #
    sqcld
    #
    @23
    cB
    c2
    @28
    @23
    @27
    cB
    cc0
    wne
    #
    @23
    @26
    @27
    @30
    wa
    dvrecg.b
    cB
    cc
    cc0
    eldifsn
    sylib
    simprd
    @20
    @23
    2z
    a1i
    expne0d
    #
    divcld
    wph
    vx
    cB
    cC
    cS
    cV
    cX
    dvrecg.s
    @28
    dvrecg.c
    dvrecg.db
    dvmptcl
    #
    mulneg1d
    @23
    @24
    @5
    @23
    @5
    @24
    @23
    cA
    cC
    @1
    @25
    @32
    @29
    @31
    div23d
    eqcomd
    negeqd
    eqtrd
    mpteq2dva
    eqtrd
end
