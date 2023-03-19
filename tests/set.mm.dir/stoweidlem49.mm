include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cv.mm"
include "cmul.mm"
include "c2.mm"
include "cdiv.mm"
include "cexp.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cn.mm"
include "wrex.mm"
include "cc0.mm"
include "cfv.mm"
include "cle.mm"
include "wral.mm"
include "cdif.mm"
include "w3a.mm"
include "crab.mm"
include "breq2.mm"
include "cbvrabv.mm"
include "stoweidlem14.mm"
include "wcel.mm"
include "cn0.mm"
include "cmpt.mm"
include "eqid.mm"
include "cr.mm"
include "nnre.mm"
include "adantl.mm"
include "rpred.mm"
include "adantr.mm"
include "remulcld.mm"
include "simprl.mm"
include "crp.mm"
include "rehalfcld.mm"
include "nngt0.mm"
include "rpgt0d.mm"
include "mulgt0d.mm"
include "2re.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "a1i.mm"
include "divgt0.mm"
include "syl21anc.mm"
include "elrpd.mm"
include "simprr.mm"
include "ad2antrr.mm"
include "stoweidlem7.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"
include "nfv.mm"
include "nfan.mm"
include "simplrr.mm"
include "simplrl.mm"
include "wf.mm"
include "ad4ant14.mm"
include "caddc.mm"
include "simp1ll.mm"
include "syld3an1.mm"
include "stoweidlem45.mm"
include "rexlimdvva.mm"

theorem stoweidlem49
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let cA: class A
  let cD: class D
  let cP: class P
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let cE: class E
  let cV: class V
  let vk: setvar k
  let vn: setvar n
  let vi: setvar i
  let vj: setvar j
  assume stoweidlem49.1: |- F/_ t P
  assume stoweidlem49.2: |- F/ t ph
  assume stoweidlem49.3: |- V = { t e. T | ( P ` t ) < ( D / 2 ) }
  assume stoweidlem49.4: |- ( ph -> D e. RR+ )
  assume stoweidlem49.5: |- ( ph -> D < 1 )
  assume stoweidlem49.6: |- ( ph -> P e. A )
  assume stoweidlem49.7: |- ( ph -> P : T --> RR )
  assume stoweidlem49.8: |- ( ph -> A. t e. T ( 0 <_ ( P ` t ) /\ ( P ` t ) <_ 1 ) )
  assume stoweidlem49.9: |- ( ph -> A. t e. ( T \ U ) D <_ ( P ` t ) )
  assume stoweidlem49.10: |- ( ( ph /\ f e. A ) -> f : T --> RR )
  assume stoweidlem49.11: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) + ( g ` t ) ) ) e. A )
  assume stoweidlem49.12: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. A )
  assume stoweidlem49.13: |- ( ( ph /\ x e. RR ) -> ( t e. T |-> x ) e. A )
  assume stoweidlem49.14: |- ( ph -> E e. RR+ )

  disjoint f g
  disjoint f t
  disjoint A f
  disjoint g t
  disjoint A g
  disjoint A t
  disjoint D f
  disjoint D g
  disjoint D t
  disjoint E f
  disjoint E g
  disjoint E t
  disjoint P f
  disjoint P g
  disjoint T f
  disjoint T g
  disjoint T t
  disjoint f ph
  disjoint g ph
  disjoint D x
  disjoint E x
  disjoint ph x
  disjoint t y
  disjoint A y
  disjoint U y
  disjoint V y
  disjoint t x
  disjoint A x
  disjoint T x
  disjoint E y
  disjoint P y
  disjoint T y
  disjoint f k
  disjoint f n
  disjoint g k
  disjoint g n
  disjoint k n
  disjoint k t
  disjoint A k
  disjoint n t
  disjoint A n
  disjoint D k
  disjoint D n
  disjoint E k
  disjoint E n
  disjoint T k
  disjoint T n
  disjoint k ph
  disjoint n ph
  disjoint i j
  disjoint i k
  disjoint i x
  disjoint D i
  disjoint j k
  disjoint j x
  disjoint D j
  disjoint k x
  disjoint i n
  disjoint n x
  disjoint E i
  disjoint i ph
  disjoint k y
  disjoint n y
  disjoint U k
  disjoint U n
  disjoint V k
  disjoint V n
  disjoint k x
  assert |- ( ph -> E. y e. A ( A. t e. T ( 0 <_ ( y ` t ) /\ ( y ` t ) <_ 1 ) /\ A. t e. V ( 1 - E ) < ( y ` t ) /\ A. t e. ( T \ U ) ( y ` t ) < E ) )

  proof
    wph
    c1
    cE
    cmin
    co
    #
    c1
    vk
    cv
    #
    cD
    cmul
    co
    #
    c2
    cdiv
    co
    #
    vn
    cv
    #
    cexp
    co
    cmin
    co
    clt
    wbr
    #
    c1
    @2
    @4
    cexp
    co
    cdiv
    co
    cE
    clt
    wbr
    #
    wa
    #
    vn
    cn
    wrex
    #
    vk
    cn
    wrex
    #
    cc0
    vt
    cv
    #
    vy
    cv
    cfv
    #
    cle
    wbr
    @11
    c1
    cle
    wbr
    wa
    vt
    cT
    wral
    @0
    @11
    clt
    wbr
    vt
    cV
    wral
    @11
    cE
    clt
    wbr
    vt
    cT
    cU
    cdif
    #
    wral
    w3a
    vy
    cA
    wrex
    #
    wph
    c1
    @2
    clt
    wbr
    #
    @3
    c1
    clt
    wbr
    #
    wa
    #
    vk
    cn
    wrex
    @9
    wph
    c1
    cD
    cdiv
    co
    #
    vj
    cv
    #
    clt
    wbr
    #
    vj
    cn
    crab
    cD
    vi
    vk
    @19
    @17
    vi
    cv
    #
    clt
    wbr
    vj
    vi
    cn
    @18
    @20
    @17
    clt
    breq2
    cbvrabv
    stoweidlem49.4
    stoweidlem49.5
    stoweidlem14
    wph
    @16
    @8
    vk
    cn
    wph
    @1
    cn
    wcel
    #
    wa
    #
    @16
    @8
    @22
    @16
    wa
    @2
    @3
    vi
    vn
    cE
    vi
    cn0
    c1
    @2
    cdiv
    co
    @20
    cexp
    co
    cmpt
    #
    vi
    cn0
    @3
    @20
    cexp
    co
    cmpt
    #
    @23
    eqid
    @24
    eqid
    @22
    @2
    cr
    wcel
    #
    @16
    @22
    @1
    cD
    @21
    @1
    cr
    wcel
    wph
    @1
    nnre
    adantl
    #
    wph
    cD
    cr
    wcel
    @21
    wph
    cD
    stoweidlem49.4
    rpred
    adantr
    #
    remulcld
    #
    adantr
    @22
    @14
    @15
    simprl
    @22
    @3
    crp
    wcel
    @16
    @22
    @3
    @22
    @2
    @28
    rehalfcld
    @22
    @25
    cc0
    @2
    clt
    wbr
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    wa
    #
    cc0
    @3
    clt
    wbr
    @28
    @22
    @1
    cD
    @26
    @27
    @21
    cc0
    @1
    clt
    wbr
    wph
    @1
    nngt0
    adantl
    wph
    cc0
    cD
    clt
    wbr
    @21
    wph
    cD
    stoweidlem49.4
    rpgt0d
    adantr
    mulgt0d
    @31
    @22
    @29
    @30
    2re
    2pos
    pm3.2i
    a1i
    @2
    c2
    divgt0
    syl21anc
    elrpd
    adantr
    @22
    @14
    @15
    simprr
    wph
    cE
    crp
    wcel
    #
    @21
    @16
    stoweidlem49.14
    ad2antrr
    stoweidlem7
    ex
    reximdva
    mpd
    wph
    @7
    @13
    vk
    vn
    cn
    cn
    wph
    @21
    @4
    cn
    wcel
    #
    wa
    #
    wa
    #
    @7
    @13
    @35
    @7
    wa
    #
    vx
    vy
    vt
    cA
    cD
    cP
    vt
    cT
    c1
    @10
    cP
    cfv
    #
    @4
    cexp
    co
    cmin
    co
    @1
    @4
    cexp
    co
    cexp
    co
    cmpt
    #
    cT
    cU
    vf
    vg
    cE
    @1
    @4
    cV
    stoweidlem49.1
    @35
    @7
    vt
    wph
    @34
    vt
    stoweidlem49.2
    @34
    vt
    nfv
    nfan
    @7
    vt
    nfv
    nfan
    stoweidlem49.3
    @38
    eqid
    wph
    @21
    @33
    @7
    simplrr
    wph
    @21
    @33
    @7
    simplrl
    wph
    cD
    crp
    wcel
    @34
    @7
    stoweidlem49.4
    ad2antrr
    wph
    cD
    c1
    clt
    wbr
    @34
    @7
    stoweidlem49.5
    ad2antrr
    wph
    cP
    cA
    wcel
    @34
    @7
    stoweidlem49.6
    ad2antrr
    wph
    cT
    cr
    cP
    wf
    @34
    @7
    stoweidlem49.7
    ad2antrr
    wph
    cc0
    @37
    cle
    wbr
    @37
    c1
    cle
    wbr
    wa
    vt
    cT
    wral
    @34
    @7
    stoweidlem49.8
    ad2antrr
    wph
    cD
    @37
    cle
    wbr
    vt
    @12
    wral
    @34
    @7
    stoweidlem49.9
    ad2antrr
    wph
    vf
    cv
    #
    cA
    wcel
    #
    cT
    cr
    @39
    wf
    @34
    @7
    stoweidlem49.10
    ad4ant14
    wph
    @40
    @36
    vg
    cv
    #
    cA
    wcel
    #
    vt
    cT
    @10
    @39
    cfv
    #
    @10
    @41
    cfv
    #
    caddc
    co
    cmpt
    cA
    wcel
    wph
    @34
    @7
    @40
    @42
    simp1ll
    #
    stoweidlem49.11
    syld3an1
    wph
    @40
    @36
    @42
    vt
    cT
    @43
    @44
    cmul
    co
    cmpt
    cA
    wcel
    @45
    stoweidlem49.12
    syld3an1
    wph
    vx
    cv
    #
    cr
    wcel
    vt
    cT
    @46
    cmpt
    cA
    wcel
    @34
    @7
    stoweidlem49.13
    ad4ant14
    wph
    @32
    @34
    @7
    stoweidlem49.14
    ad2antrr
    @35
    @5
    @6
    simprl
    @35
    @5
    @6
    simprr
    stoweidlem45
    ex
    rexlimdvva
    mpd
end
