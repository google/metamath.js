include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "cop.mm"
include "cdm.mm"
include "cvv.mm"
include "w3a.mm"
include "brovpreldm.mm"
include "copab.mm"
include "cmpt2.mm"
include "wi.mm"
include "cmpt.mm"
include "wceq.mm"
include "a1i.mm"
include "cv.mm"
include "opabbidv.mm"
include "mpt2eq123dv.mm"
include "adantl.mm"
include "simpl.mm"
include "simpr.mm"
include "fvmptd.mm"
include "dmeqd.mm"
include "eleq2d.mm"
include "coprab.mm"
include "cxp.mm"
include "dmoprabss.mm"
include "sseli.mm"
include "bropfvvvvlem.mm"
include "ex.mm"
include "syl.mm"
include "df-mpt2.mm"
include "dmeqi.mm"
include "eleq2s.mm"
include "syl6bi.mm"
include "com23.mm"
include "a1d.mm"
include "wn.mm"
include "wo.mm"
include "ianor.mm"
include "c0.mm"
include "fvmptndm.mm"
include "dm0.mm"
include "eleq2i.mm"
include "syl6bb.mm"
include "noel.mm"
include "pm2.21i.mm"
include "notnotb.mm"
include "elex.mm"
include "anim12i.mm"
include "mpt2exga.mm"
include "pm2.24d.mm"
include "sylbir.mm"
include "imp.mm"
include "jaoi3.mm"
include "sylbi.mm"
include "com34.mm"
include "pm2.61i.mm"
include "mpdi.mm"

theorem bropfvvvv
  let wph: wff ph
  let wps: wff ps
  let wth: wff th
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let cU: class U
  let ve: setvar e
  let cE: class E
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vz: setvar z
  assume bropfvvvv.o: |- O = ( a e. U |-> ( b e. V , c e. W |-> { <. d , e >. | ph } ) )
  assume bropfvvvv.oo: |- ( ( A e. U /\ B e. S /\ C e. T ) -> ( B ( O ` A ) C ) = { <. d , e >. | th } )
  assume bropfvvvv.s: |- ( a = A -> V = S )
  assume bropfvvvv.t: |- ( a = A -> W = T )
  assume bropfvvvv.p: |- ( a = A -> ( ph <-> ps ) )

  disjoint U a
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A d
  disjoint A e
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint c d
  disjoint c e
  disjoint d e
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint T a
  disjoint T b
  disjoint T c
  disjoint a ps
  disjoint S z
  disjoint b z
  disjoint c z
  disjoint T z
  disjoint ps z
  disjoint d z
  disjoint e z
  assert |- ( ( S e. X /\ T e. Y ) -> ( D ( B ( O ` A ) C ) E -> ( A e. U /\ ( B e. S /\ C e. T ) /\ ( D e. _V /\ E e. _V ) ) ) )

  proof
    cS
    cX
    wcel
    #
    cT
    cY
    wcel
    #
    wa
    #
    cD
    cE
    cB
    cC
    cA
    cO
    cfv
    #
    co
    wbr
    #
    cB
    cC
    cop
    #
    @3
    cdm
    #
    wcel
    #
    cA
    cU
    wcel
    #
    cB
    cS
    wcel
    cC
    cT
    wcel
    wa
    cD
    cvv
    wcel
    cE
    cvv
    wcel
    wa
    w3a
    #
    @3
    cB
    cC
    cD
    cE
    brovpreldm
    @8
    vb
    vc
    cS
    cT
    wps
    vd
    ve
    copab
    #
    cmpt2
    #
    cvv
    wcel
    #
    wa
    #
    @2
    @4
    @7
    @9
    wi
    wi
    #
    wi
    @13
    @14
    @2
    @13
    @7
    @4
    @9
    @13
    @7
    @5
    @11
    cdm
    #
    wcel
    @4
    @9
    wi
    #
    @13
    @6
    @15
    @5
    @13
    @3
    @11
    @13
    va
    cA
    vb
    vc
    cV
    cW
    wph
    vd
    ve
    copab
    #
    cmpt2
    #
    @11
    cU
    cO
    cvv
    cO
    va
    cU
    @18
    cmpt
    wceq
    @13
    bropfvvvv.o
    a1i
    va
    cv
    cA
    wceq
    #
    @18
    @11
    wceq
    @13
    @19
    vb
    vc
    cV
    cW
    @17
    cS
    cT
    @10
    bropfvvvv.s
    bropfvvvv.t
    @19
    wph
    wps
    vd
    ve
    bropfvvvv.p
    opabbidv
    mpt2eq123dv
    adantl
    @8
    @12
    simpl
    @8
    @12
    simpr
    fvmptd
    dmeqd
    eleq2d
    @16
    @5
    vb
    cv
    cS
    wcel
    vc
    cv
    cT
    wcel
    wa
    vz
    cv
    @10
    wceq
    #
    wa
    vb
    vc
    vz
    coprab
    #
    cdm
    #
    @15
    @5
    @22
    wcel
    @5
    cS
    cT
    cxp
    #
    wcel
    #
    @16
    @22
    @23
    @5
    @20
    vb
    vc
    vz
    cS
    cT
    dmoprabss
    sseli
    @24
    @4
    @9
    wph
    wth
    cA
    cB
    cC
    cD
    cS
    cT
    cU
    ve
    cE
    cO
    cV
    cW
    va
    vb
    vc
    vd
    bropfvvvv.o
    bropfvvvv.oo
    bropfvvvvlem
    ex
    syl
    @11
    @21
    vb
    vc
    vz
    cS
    cT
    @10
    df-mpt2
    dmeqi
    eleq2s
    syl6bi
    com23
    a1d
    @13
    wn
    #
    @2
    @7
    @4
    @9
    @25
    @8
    wn
    #
    @12
    wn
    #
    wo
    @2
    @7
    @16
    wi
    #
    wi
    #
    @8
    @12
    ianor
    @26
    @29
    @27
    @26
    @28
    @2
    @26
    @7
    @5
    c0
    wcel
    #
    @16
    @26
    @7
    @5
    c0
    cdm
    #
    wcel
    @30
    @26
    @6
    @31
    @5
    @26
    @3
    c0
    va
    cU
    @18
    cO
    cA
    bropfvvvv.o
    fvmptndm
    dmeqd
    eleq2d
    @31
    c0
    @5
    dm0
    eleq2i
    syl6bb
    @30
    @16
    @5
    noel
    pm2.21i
    syl6bi
    a1d
    @26
    wn
    #
    @27
    @29
    @32
    @8
    @27
    @29
    wi
    @8
    notnotb
    @8
    @2
    @27
    @28
    @8
    @2
    @27
    @28
    wi
    @8
    @2
    wa
    #
    @12
    @28
    @33
    cS
    cvv
    wcel
    #
    cT
    cvv
    wcel
    #
    wa
    #
    @12
    @2
    @36
    @8
    @0
    @34
    @1
    @35
    cS
    cX
    elex
    cT
    cY
    elex
    anim12i
    adantl
    vb
    vc
    cS
    cT
    @10
    cvv
    cvv
    mpt2exga
    syl
    pm2.24d
    ex
    com23
    sylbir
    imp
    jaoi3
    sylbi
    com34
    pm2.61i
    mpdi
end
