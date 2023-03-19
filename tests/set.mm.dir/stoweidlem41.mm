include "wcel.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "wa.mm"
include "wral.mm"
include "clt.mm"
include "cmin.mm"
include "co.mm"
include "cdif.mm"
include "w3a.mm"
include "wrex.mm"
include "cmpt.mm"
include "wceq.mm"
include "cr.mm"
include "1re.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "adantl.mm"
include "oveq1d.mm"
include "mpteq2da.mm"
include "syl6eqr.mm"
include "stoweidlem4.mm"
include "syl5eqel.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nfcv.mm"
include "stoweidlem33.mm"
include "mpd3an23.mm"
include "eqeltrrd.mm"
include "ffvelrnda.mm"
include "1red.mm"
include "0red.mm"
include "r19.21bi.mm"
include "simprd.mm"
include "1m0e1.mm"
include "syl6breqr.mm"
include "lesubd.mm"
include "simpr.mm"
include "resubcld.mm"
include "syl2anc.mm"
include "breqtrrd.mm"
include "simpld.mm"
include "lesub2dd.mm"
include "syl6breq.mm"
include "eqbrtrd.mm"
include "jca.mm"
include "ex.mm"
include "ralrimi.mm"
include "sseli.mm"
include "sylan2.mm"
include "rpred.mm"
include "adantr.mm"
include "ltsub23d.mm"
include "eldifi.mm"
include "ltsub2dd.mm"
include "nfeq2.mm"
include "fveq1.mm"
include "breq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "ralbid.mm"
include "3anbi123d.mm"
include "rspcev.mm"
include "syl13anc.mm"

theorem stoweidlem41
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vt: setvar t
  let cA: class A
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let cE: class E
  let cF: class F
  let cV: class V
  let cX: class X
  let vk: setvar k
  assume stoweidlem41.1: |- F/ t ph
  assume stoweidlem41.2: |- X = ( t e. T |-> ( 1 - ( y ` t ) ) )
  assume stoweidlem41.3: |- F = ( t e. T |-> 1 )
  assume stoweidlem41.4: |- V C_ T
  assume stoweidlem41.5: |- ( ph -> y e. A )
  assume stoweidlem41.6: |- ( ph -> y : T --> RR )
  assume stoweidlem41.7: |- ( ( ph /\ f e. A ) -> f : T --> RR )
  assume stoweidlem41.8: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) + ( g ` t ) ) ) e. A )
  assume stoweidlem41.9: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. A )
  assume stoweidlem41.10: |- ( ( ph /\ w e. RR ) -> ( t e. T |-> w ) e. A )
  assume stoweidlem41.11: |- ( ph -> E e. RR+ )
  assume stoweidlem41.12: |- ( ph -> A. t e. T ( 0 <_ ( y ` t ) /\ ( y ` t ) <_ 1 ) )
  assume stoweidlem41.13: |- ( ph -> A. t e. V ( 1 - E ) < ( y ` t ) )
  assume stoweidlem41.14: |- ( ph -> A. t e. ( T \ U ) ( y ` t ) < E )

  disjoint f g
  disjoint f t
  disjoint f y
  disjoint g t
  disjoint g y
  disjoint t y
  disjoint A f
  disjoint A g
  disjoint A t
  disjoint F f
  disjoint F g
  disjoint T f
  disjoint T g
  disjoint T t
  disjoint f ph
  disjoint g ph
  disjoint t w
  disjoint A w
  disjoint t x
  disjoint A x
  disjoint T w
  disjoint ph w
  disjoint E x
  disjoint T x
  disjoint U x
  disjoint V x
  disjoint X x
  disjoint k x
  assert |- ( ph -> E. x e. A ( A. t e. T ( 0 <_ ( x ` t ) /\ ( x ` t ) <_ 1 ) /\ A. t e. V ( x ` t ) < E /\ A. t e. ( T \ U ) ( 1 - E ) < ( x ` t ) ) )

  proof
    wph
    cX
    cA
    wcel
    cc0
    vt
    cv
    #
    cX
    cfv
    #
    cle
    wbr
    #
    @1
    c1
    cle
    wbr
    #
    wa
    #
    vt
    cT
    wral
    #
    @1
    cE
    clt
    wbr
    #
    vt
    cV
    wral
    #
    c1
    cE
    cmin
    co
    #
    @1
    clt
    wbr
    #
    vt
    cT
    cU
    cdif
    #
    wral
    #
    cc0
    @0
    vx
    cv
    #
    cfv
    #
    cle
    wbr
    #
    @13
    c1
    cle
    wbr
    #
    wa
    #
    vt
    cT
    wral
    #
    @13
    cE
    clt
    wbr
    #
    vt
    cV
    wral
    #
    @8
    @13
    clt
    wbr
    #
    vt
    @10
    wral
    #
    w3a
    #
    vx
    cA
    wrex
    wph
    vt
    cT
    @0
    cF
    cfv
    #
    @0
    vy
    cv
    #
    cfv
    #
    cmin
    co
    #
    cmpt
    #
    cX
    cA
    wph
    @27
    vt
    cT
    c1
    @25
    cmin
    co
    #
    cmpt
    #
    cX
    wph
    vt
    cT
    @26
    @28
    stoweidlem41.1
    wph
    @0
    cT
    wcel
    #
    wa
    #
    @23
    c1
    @25
    cmin
    @30
    @23
    c1
    wceq
    #
    wph
    @30
    c1
    cr
    wcel
    #
    @32
    1re
    vt
    cT
    c1
    cr
    cF
    stoweidlem41.3
    fvmpt2
    mpan2
    adantl
    oveq1d
    mpteq2da
    stoweidlem41.2
    syl6eqr
    wph
    cF
    cA
    wcel
    @24
    cA
    wcel
    @27
    cA
    wcel
    wph
    cF
    vt
    cT
    c1
    cmpt
    #
    cA
    stoweidlem41.3
    wph
    @33
    @34
    cA
    wcel
    1re
    wph
    vw
    vt
    cA
    c1
    cT
    stoweidlem41.10
    stoweidlem4
    mpan2
    syl5eqel
    stoweidlem41.5
    wph
    vw
    vt
    cA
    cT
    vf
    vg
    cF
    @24
    vt
    cF
    @34
    stoweidlem41.3
    vt
    cT
    c1
    nfmpt1
    nfcxfr
    vt
    @24
    nfcv
    stoweidlem41.1
    stoweidlem41.7
    stoweidlem41.8
    stoweidlem41.9
    stoweidlem41.10
    stoweidlem33
    mpd3an23
    eqeltrrd
    wph
    @4
    vt
    cT
    stoweidlem41.1
    wph
    @30
    @4
    @31
    @2
    @3
    @31
    cc0
    @28
    @1
    cle
    @31
    @25
    c1
    cc0
    wph
    cT
    cr
    @0
    @24
    stoweidlem41.6
    ffvelrnda
    #
    @31
    1red
    #
    @31
    0red
    #
    @31
    @25
    c1
    c1
    cc0
    cmin
    co
    #
    cle
    @31
    cc0
    @25
    cle
    wbr
    #
    @25
    c1
    cle
    wbr
    #
    wph
    @39
    @40
    wa
    vt
    cT
    stoweidlem41.12
    r19.21bi
    #
    simprd
    1m0e1
    syl6breqr
    lesubd
    @31
    @30
    @28
    cr
    wcel
    @1
    @28
    wceq
    #
    wph
    @30
    simpr
    @31
    c1
    @25
    @36
    @35
    resubcld
    vt
    cT
    @28
    cr
    cX
    stoweidlem41.2
    fvmpt2
    syl2anc
    #
    breqtrrd
    @31
    @1
    @28
    c1
    cle
    @43
    @31
    @28
    @38
    c1
    cle
    @31
    cc0
    @25
    c1
    @37
    @35
    @36
    @31
    @39
    @40
    @41
    simpld
    lesub2dd
    1m0e1
    syl6breq
    eqbrtrd
    jca
    ex
    ralrimi
    wph
    @6
    vt
    cV
    stoweidlem41.1
    wph
    @0
    cV
    wcel
    #
    @6
    wph
    @44
    wa
    #
    @1
    @28
    cE
    clt
    @44
    wph
    @30
    @42
    cV
    cT
    @0
    stoweidlem41.4
    sseli
    #
    @43
    sylan2
    @45
    c1
    cE
    @25
    @45
    1red
    wph
    cE
    cr
    wcel
    #
    @44
    wph
    cE
    stoweidlem41.11
    rpred
    #
    adantr
    @44
    wph
    @30
    @25
    cr
    wcel
    #
    @46
    @35
    sylan2
    wph
    @8
    @25
    clt
    wbr
    vt
    cV
    stoweidlem41.13
    r19.21bi
    ltsub23d
    eqbrtrd
    ex
    ralrimi
    wph
    @9
    vt
    @10
    stoweidlem41.1
    wph
    @0
    @10
    wcel
    #
    @9
    wph
    @50
    wa
    #
    @8
    @28
    @1
    clt
    @51
    @25
    cE
    c1
    @50
    wph
    @30
    @49
    @0
    cT
    cU
    eldifi
    #
    @35
    sylan2
    wph
    @47
    @50
    @48
    adantr
    @51
    1red
    wph
    @25
    cE
    clt
    wbr
    vt
    @10
    stoweidlem41.14
    r19.21bi
    ltsub2dd
    @50
    wph
    @30
    @42
    @52
    @43
    sylan2
    breqtrrd
    ex
    ralrimi
    @22
    @5
    @7
    @11
    w3a
    vx
    cX
    cA
    @12
    cX
    wceq
    #
    @17
    @5
    @19
    @7
    @21
    @11
    @53
    @16
    @4
    vt
    cT
    vt
    @12
    cX
    vt
    cX
    @29
    stoweidlem41.2
    vt
    cT
    @28
    nfmpt1
    nfcxfr
    nfeq2
    #
    @53
    @14
    @2
    @15
    @3
    @53
    @13
    @1
    cc0
    cle
    @0
    @12
    cX
    fveq1
    #
    breq2d
    @53
    @13
    @1
    c1
    cle
    @55
    breq1d
    anbi12d
    ralbid
    @53
    @18
    @6
    vt
    cV
    @54
    @53
    @13
    @1
    cE
    clt
    @55
    breq1d
    ralbid
    @53
    @20
    @9
    vt
    @10
    @54
    @53
    @13
    @1
    @8
    clt
    @55
    breq2d
    ralbid
    3anbi123d
    rspcev
    syl13anc
end
