include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "c1.mm"
include "cmin.mm"
include "cmul.mm"
include "caddc.mm"
include "cfz.mm"
include "wral.mm"
include "wf1o.mm"
include "wf.mm"
include "axcontlem2.mm"
include "f1of.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "wi.mm"
include "simpl.mm"
include "a1i.mm"
include "wb.mm"
include "wbr.mm"
include "wfn.mm"
include "f1ofn.mm"
include "fnbrfvb.mm"
include "sylan.mm"
include "3adant3.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "anbi2d.mm"
include "anbi12d.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "eqeq2d.mm"
include "anass.mm"
include "anidm.mm"
include "anbi2i.mm"
include "bitr2i.mm"
include "anbi1i.mm"
include "3bitr3i.mm"
include "syl6bb.mm"
include "brabg.mm"
include "bianabs.mm"
include "3adant1.mm"
include "bitrd.mm"
include "3expia.mm"
include "pm5.21ndd.mm"

theorem axcontlem5
  let vx: setvar x
  let vt: setvar t
  let cD: class D
  let cP: class P
  let cT: class T
  let cU: class U
  let vi: setvar i
  let cF: class F
  let cN: class N
  let cZ: class Z
  let vp: setvar p
  assume axcontlem5.1: |- D = { p e. ( EE ` N ) | ( U Btwn <. Z , p >. \/ p Btwn <. Z , U >. ) }
  assume axcontlem5.2: |- F = { <. x , t >. | ( x e. D /\ ( t e. ( 0 [,) +oo ) /\ A. i e. ( 1 ... N ) ( x ` i ) = ( ( ( 1 - t ) x. ( Z ` i ) ) + ( t x. ( U ` i ) ) ) ) ) }

  disjoint D t
  disjoint t x
  disjoint D x
  disjoint i p
  disjoint i t
  disjoint i x
  disjoint N i
  disjoint p t
  disjoint p x
  disjoint N p
  disjoint N t
  disjoint N x
  disjoint P i
  disjoint P t
  disjoint P x
  disjoint T x
  disjoint T i
  disjoint T t
  disjoint U i
  disjoint U p
  disjoint U t
  disjoint U x
  disjoint Z i
  disjoint Z p
  disjoint Z t
  disjoint Z x
  assert |- ( ( ( ( N e. NN /\ Z e. ( EE ` N ) /\ U e. ( EE ` N ) ) /\ Z =/= U ) /\ P e. D ) -> ( ( F ` P ) = T <-> ( T e. ( 0 [,) +oo ) /\ A. i e. ( 1 ... N ) ( P ` i ) = ( ( ( 1 - T ) x. ( Z ` i ) ) + ( T x. ( U ` i ) ) ) ) ) )

  proof
    cN
    cn
    wcel
    cZ
    cN
    cee
    cfv
    #
    wcel
    cU
    @0
    wcel
    w3a
    cZ
    cU
    wne
    wa
    #
    cP
    cD
    wcel
    #
    wa
    #
    cT
    cc0
    cpnf
    cico
    co
    #
    wcel
    #
    cP
    cF
    cfv
    #
    cT
    wceq
    #
    @5
    vi
    cv
    #
    cP
    cfv
    #
    c1
    cT
    cmin
    co
    #
    @8
    cZ
    cfv
    #
    cmul
    co
    #
    cT
    @8
    cU
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vi
    c1
    cN
    cfz
    co
    #
    wral
    #
    wa
    #
    @3
    @6
    @4
    wcel
    @7
    @5
    @1
    cD
    @4
    cP
    cF
    @1
    cD
    @4
    cF
    wf1o
    #
    cD
    @4
    cF
    wf
    vx
    vt
    cD
    cU
    vi
    cF
    cN
    cZ
    vp
    axcontlem5.1
    axcontlem5.2
    axcontlem2
    #
    cD
    @4
    cF
    f1of
    syl
    ffvelrnda
    @6
    cT
    @4
    eleq1
    syl5ibcom
    @19
    @5
    wi
    @3
    @5
    @18
    simpl
    a1i
    @1
    @2
    @5
    @7
    @19
    wb
    @1
    @2
    @5
    w3a
    @7
    cP
    cT
    cF
    wbr
    #
    @19
    @1
    @2
    @7
    @22
    wb
    #
    @5
    @1
    cF
    cD
    wfn
    #
    @2
    @23
    @1
    @20
    @24
    @21
    cD
    @4
    cF
    f1ofn
    syl
    cD
    cP
    cT
    cF
    fnbrfvb
    sylan
    3adant3
    @2
    @5
    @22
    @19
    wb
    @1
    @2
    @5
    wa
    #
    @22
    @19
    vx
    cv
    #
    cD
    wcel
    #
    vt
    cv
    #
    @4
    wcel
    #
    @8
    @26
    cfv
    #
    c1
    @28
    cmin
    co
    #
    @11
    cmul
    co
    #
    @28
    @13
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vi
    @17
    wral
    #
    wa
    #
    wa
    @2
    @29
    @9
    @34
    wceq
    #
    vi
    @17
    wral
    #
    wa
    #
    wa
    #
    @25
    @19
    wa
    #
    vx
    vt
    cP
    cT
    cD
    @4
    cF
    @26
    cP
    wceq
    #
    @27
    @2
    @37
    @40
    @26
    cP
    cD
    eleq1
    @43
    @36
    @39
    @29
    @43
    @35
    @38
    vi
    @17
    @43
    @30
    @9
    @34
    @8
    @26
    cP
    fveq1
    eqeq1d
    ralbidv
    anbi2d
    anbi12d
    @28
    cT
    wceq
    #
    @41
    @2
    @19
    wa
    #
    @42
    @44
    @40
    @19
    @2
    @44
    @29
    @5
    @39
    @18
    @28
    cT
    @4
    eleq1
    @44
    @38
    @16
    vi
    @17
    @44
    @34
    @15
    @9
    @44
    @32
    @12
    @33
    @14
    caddc
    @44
    @31
    @10
    @11
    cmul
    @28
    cT
    c1
    cmin
    oveq2
    oveq1d
    @28
    cT
    @13
    cmul
    oveq1
    oveq12d
    eqeq2d
    ralbidv
    anbi12d
    anbi2d
    @25
    @18
    wa
    @25
    @5
    wa
    #
    @18
    wa
    @45
    @42
    @25
    @46
    @18
    @46
    @2
    @5
    @5
    wa
    #
    wa
    @25
    @2
    @5
    @5
    anass
    @47
    @5
    @2
    @5
    anidm
    anbi2i
    bitr2i
    anbi1i
    @2
    @5
    @18
    anass
    @25
    @5
    @18
    anass
    3bitr3i
    syl6bb
    axcontlem5.2
    brabg
    bianabs
    3adant1
    bitrd
    3expia
    pm5.21ndd
end
