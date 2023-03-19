include "wcel.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "wa.mm"
include "wral.mm"
include "cmin.mm"
include "co.mm"
include "clt.mm"
include "cdif.mm"
include "w3a.mm"
include "wrex.mm"
include "cexp.mm"
include "cmpt.mm"
include "eqid.mm"
include "nnnn0d.mm"
include "nnexpcld.mm"
include "stoweidlem40.mm"
include "1red.mm"
include "cr.mm"
include "ffvelrnda.mm"
include "cn0.mm"
include "adantr.mm"
include "reexpcld.mm"
include "resubcld.mm"
include "nn0expcld.mm"
include "1m1e0.mm"
include "r19.21bi.mm"
include "simpld.mm"
include "simprd.mm"
include "exple1.mm"
include "syl31anc.mm"
include "lesub2dd.mm"
include "syl5eqbrr.mm"
include "expge0d.mm"
include "stoweidlem12.mm"
include "breqtrrd.mm"
include "0red.mm"
include "1m0e1.mm"
include "syl6breq.mm"
include "eqbrtrd.mm"
include "jca.mm"
include "ex.mm"
include "ralrimi.mm"
include "stoweidlem24.mm"
include "stoweidlem25.mm"
include "wceq.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nfeq2.mm"
include "fveq1.mm"
include "breq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "ralbid.mm"
include "3anbi123d.mm"
include "rspcev.mm"
include "syl13anc.mm"

theorem stoweidlem45
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let cA: class A
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let cE: class E
  let cK: class K
  let cN: class N
  let cV: class V
  let vk: setvar k
  assume stoweidlem45.1: |- F/_ t P
  assume stoweidlem45.2: |- F/ t ph
  assume stoweidlem45.3: |- V = { t e. T | ( P ` t ) < ( D / 2 ) }
  assume stoweidlem45.4: |- Q = ( t e. T |-> ( ( 1 - ( ( P ` t ) ^ N ) ) ^ ( K ^ N ) ) )
  assume stoweidlem45.5: |- ( ph -> N e. NN )
  assume stoweidlem45.6: |- ( ph -> K e. NN )
  assume stoweidlem45.7: |- ( ph -> D e. RR+ )
  assume stoweidlem45.8: |- ( ph -> D < 1 )
  assume stoweidlem45.9: |- ( ph -> P e. A )
  assume stoweidlem45.10: |- ( ph -> P : T --> RR )
  assume stoweidlem45.11: |- ( ph -> A. t e. T ( 0 <_ ( P ` t ) /\ ( P ` t ) <_ 1 ) )
  assume stoweidlem45.12: |- ( ph -> A. t e. ( T \ U ) D <_ ( P ` t ) )
  assume stoweidlem45.13: |- ( ( ph /\ f e. A ) -> f : T --> RR )
  assume stoweidlem45.14: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) + ( g ` t ) ) ) e. A )
  assume stoweidlem45.15: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. A )
  assume stoweidlem45.16: |- ( ( ph /\ x e. RR ) -> ( t e. T |-> x ) e. A )
  assume stoweidlem45.17: |- ( ph -> E e. RR+ )
  assume stoweidlem45.18: |- ( ph -> ( 1 - E ) < ( 1 - ( ( ( K x. D ) / 2 ) ^ N ) ) )
  assume stoweidlem45.19: |- ( ph -> ( 1 / ( ( K x. D ) ^ N ) ) < E )

  disjoint f g
  disjoint f t
  disjoint A f
  disjoint g t
  disjoint A g
  disjoint A t
  disjoint N f
  disjoint N g
  disjoint N t
  disjoint P f
  disjoint P g
  disjoint T f
  disjoint T g
  disjoint T t
  disjoint f ph
  disjoint g ph
  disjoint t x
  disjoint A x
  disjoint t y
  disjoint A y
  disjoint K t
  disjoint T x
  disjoint ph x
  disjoint E y
  disjoint Q y
  disjoint T y
  disjoint U y
  disjoint V y
  disjoint k x
  assert |- ( ph -> E. y e. A ( A. t e. T ( 0 <_ ( y ` t ) /\ ( y ` t ) <_ 1 ) /\ A. t e. V ( 1 - E ) < ( y ` t ) /\ A. t e. ( T \ U ) ( y ` t ) < E ) )

  proof
    wph
    cQ
    cA
    wcel
    cc0
    vt
    cv
    #
    cQ
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
    cV
    wral
    #
    @1
    cE
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
    vy
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
    @6
    @13
    clt
    wbr
    #
    vt
    cV
    wral
    #
    @13
    cE
    clt
    wbr
    #
    vt
    @10
    wral
    #
    w3a
    #
    vy
    cA
    wrex
    wph
    vx
    vt
    cA
    cP
    cQ
    cT
    vf
    vg
    vt
    cT
    c1
    @0
    cP
    cfv
    #
    cN
    cexp
    co
    #
    cmin
    co
    #
    cmpt
    #
    vt
    cT
    c1
    cmpt
    #
    vt
    cT
    @24
    cmpt
    #
    cK
    cN
    cexp
    co
    #
    cN
    stoweidlem45.1
    stoweidlem45.2
    stoweidlem45.4
    @26
    eqid
    @27
    eqid
    @28
    eqid
    stoweidlem45.9
    stoweidlem45.10
    stoweidlem45.13
    stoweidlem45.14
    stoweidlem45.15
    stoweidlem45.16
    stoweidlem45.5
    wph
    cK
    cN
    stoweidlem45.6
    wph
    cN
    stoweidlem45.5
    nnnn0d
    #
    nnexpcld
    stoweidlem40
    wph
    @4
    vt
    cT
    stoweidlem45.2
    wph
    @0
    cT
    wcel
    #
    @4
    wph
    @31
    wa
    #
    @2
    @3
    @32
    cc0
    @25
    @29
    cexp
    co
    #
    @1
    cle
    @32
    @25
    @29
    @32
    c1
    @24
    @32
    1red
    #
    @32
    @23
    cN
    wph
    cT
    cr
    @0
    cP
    stoweidlem45.10
    ffvelrnda
    #
    wph
    cN
    cn0
    wcel
    #
    @31
    @30
    adantr
    #
    reexpcld
    #
    resubcld
    #
    wph
    @29
    cn0
    wcel
    #
    @31
    wph
    cK
    cN
    wph
    cK
    stoweidlem45.6
    nnnn0d
    #
    @30
    nn0expcld
    adantr
    #
    @32
    cc0
    c1
    c1
    cmin
    co
    @25
    cle
    1m1e0
    @32
    @24
    c1
    c1
    @38
    @34
    @34
    @32
    @23
    cr
    wcel
    cc0
    @23
    cle
    wbr
    #
    @23
    c1
    cle
    wbr
    #
    @36
    @24
    c1
    cle
    wbr
    @35
    @32
    @43
    @44
    wph
    @43
    @44
    wa
    vt
    cT
    stoweidlem45.11
    r19.21bi
    #
    simpld
    #
    @32
    @43
    @44
    @45
    simprd
    @37
    @23
    cN
    exple1
    syl31anc
    lesub2dd
    syl5eqbrr
    #
    expge0d
    wph
    vt
    cP
    cQ
    cT
    cK
    cN
    stoweidlem45.4
    stoweidlem45.10
    @30
    @41
    stoweidlem12
    #
    breqtrrd
    @32
    @1
    @33
    c1
    cle
    @48
    @32
    @25
    cr
    wcel
    cc0
    @25
    cle
    wbr
    @25
    c1
    cle
    wbr
    @40
    @33
    c1
    cle
    wbr
    @39
    @47
    @32
    @25
    c1
    cc0
    cmin
    co
    c1
    cle
    @32
    cc0
    @24
    c1
    @32
    0red
    @38
    @34
    @32
    @23
    cN
    @35
    @37
    @46
    expge0d
    lesub2dd
    1m0e1
    syl6breq
    @42
    @25
    @29
    exple1
    syl31anc
    eqbrtrd
    jca
    ex
    ralrimi
    wph
    @7
    vt
    cV
    stoweidlem45.2
    wph
    @0
    cV
    wcel
    @7
    wph
    vt
    cD
    cP
    cQ
    cT
    cE
    cK
    cN
    cV
    stoweidlem45.3
    stoweidlem45.4
    stoweidlem45.10
    @30
    @41
    stoweidlem45.7
    stoweidlem45.17
    stoweidlem45.18
    stoweidlem45.11
    stoweidlem24
    ex
    ralrimi
    wph
    @9
    vt
    @10
    stoweidlem45.2
    wph
    @0
    @10
    wcel
    @9
    wph
    vt
    cD
    cP
    cQ
    cT
    cU
    cE
    cK
    cN
    stoweidlem45.4
    stoweidlem45.5
    stoweidlem45.6
    stoweidlem45.7
    stoweidlem45.10
    stoweidlem45.11
    stoweidlem45.12
    stoweidlem45.17
    stoweidlem45.19
    stoweidlem25
    ex
    ralrimi
    @22
    @5
    @8
    @11
    w3a
    vy
    cQ
    cA
    @12
    cQ
    wceq
    #
    @17
    @5
    @19
    @8
    @21
    @11
    @49
    @16
    @4
    vt
    cT
    vt
    @12
    cQ
    vt
    cQ
    vt
    cT
    @33
    cmpt
    stoweidlem45.4
    vt
    cT
    @33
    nfmpt1
    nfcxfr
    nfeq2
    #
    @49
    @14
    @2
    @15
    @3
    @49
    @13
    @1
    cc0
    cle
    @0
    @12
    cQ
    fveq1
    #
    breq2d
    @49
    @13
    @1
    c1
    cle
    @51
    breq1d
    anbi12d
    ralbid
    @49
    @18
    @7
    vt
    cV
    @50
    @49
    @13
    @1
    @6
    clt
    @51
    breq2d
    ralbid
    @49
    @20
    @9
    vt
    @10
    @50
    @49
    @13
    @1
    cE
    clt
    @51
    breq1d
    ralbid
    3anbi123d
    rspcev
    syl13anc
end
