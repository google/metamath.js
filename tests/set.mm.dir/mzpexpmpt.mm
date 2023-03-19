include "cn0.mm"
include "wcel.mm"
include "cz.mm"
include "cmap.mm"
include "co.mm"
include "cmpt.mm"
include "cmzp.mm"
include "cfv.mm"
include "cexp.mm"
include "cv.mm"
include "wi.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "oveq2.mm"
include "mpteq2dv.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "cc.mm"
include "wral.mm"
include "wf.mm"
include "wss.mm"
include "mzpf.mm"
include "zsscn.mm"
include "fss.mm"
include "sylancl.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylibr.mm"
include "nfra1.mm"
include "wa.mm"
include "rspa.mm"
include "exp0d.mm"
include "mpteq2da.mm"
include "syl.mm"
include "cvv.mm"
include "elfvex.mm"
include "1z.mm"
include "mzpconstmpt.mm"
include "eqeltrd.mm"
include "w3a.mm"
include "cmul.mm"
include "3ad2ant2.mm"
include "simp1.mm"
include "nfv.mm"
include "nfan.mm"
include "adantlr.mm"
include "simplr.mm"
include "expp1d.mm"
include "syl2anc.mm"
include "simp3.mm"
include "simp2.mm"
include "mzpmulmpt.mm"
include "3exp.mm"
include "a2d.mm"
include "nn0ind.mm"
include "impcom.mm"

theorem mzpexpmpt
  let vx: setvar x
  let cA: class A
  let cD: class D
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let cC: class C

  disjoint V x
  disjoint D x
  disjoint V a
  disjoint V b
  disjoint a x
  disjoint b x
  disjoint a b
  disjoint C x
  disjoint D a
  disjoint D b
  disjoint A a
  disjoint A b
  assert |- ( ( ( x e. ( ZZ ^m V ) |-> A ) e. ( mzPoly ` V ) /\ D e. NN0 ) -> ( x e. ( ZZ ^m V ) |-> ( A ^ D ) ) e. ( mzPoly ` V ) )

  proof
    cD
    cn0
    wcel
    vx
    cz
    cV
    cmap
    co
    #
    cA
    cmpt
    #
    cV
    cmzp
    cfv
    #
    wcel
    #
    vx
    @0
    cA
    cD
    cexp
    co
    #
    cmpt
    #
    @2
    wcel
    #
    @3
    vx
    @0
    cA
    va
    cv
    #
    cexp
    co
    #
    cmpt
    #
    @2
    wcel
    #
    wi
    @3
    vx
    @0
    cA
    cc0
    cexp
    co
    #
    cmpt
    #
    @2
    wcel
    #
    wi
    @3
    vx
    @0
    cA
    vb
    cv
    #
    cexp
    co
    #
    cmpt
    #
    @2
    wcel
    #
    wi
    @3
    vx
    @0
    cA
    @14
    c1
    caddc
    co
    #
    cexp
    co
    #
    cmpt
    #
    @2
    wcel
    #
    wi
    @3
    @6
    wi
    va
    vb
    cD
    @7
    cc0
    wceq
    #
    @10
    @13
    @3
    @22
    @9
    @12
    @2
    @22
    vx
    @0
    @8
    @11
    @7
    cc0
    cA
    cexp
    oveq2
    mpteq2dv
    eleq1d
    imbi2d
    @7
    @14
    wceq
    #
    @10
    @17
    @3
    @23
    @9
    @16
    @2
    @23
    vx
    @0
    @8
    @15
    @7
    @14
    cA
    cexp
    oveq2
    mpteq2dv
    eleq1d
    imbi2d
    @7
    @18
    wceq
    #
    @10
    @21
    @3
    @24
    @9
    @20
    @2
    @24
    vx
    @0
    @8
    @19
    @7
    @18
    cA
    cexp
    oveq2
    mpteq2dv
    eleq1d
    imbi2d
    @7
    cD
    wceq
    #
    @10
    @6
    @3
    @25
    @9
    @5
    @2
    @25
    vx
    @0
    @8
    @4
    @7
    cD
    cA
    cexp
    oveq2
    mpteq2dv
    eleq1d
    imbi2d
    @3
    @12
    vx
    @0
    c1
    cmpt
    #
    @2
    @3
    cA
    cc
    wcel
    #
    vx
    @0
    wral
    #
    @12
    @26
    wceq
    @3
    @0
    cc
    @1
    wf
    #
    @28
    @3
    @0
    cz
    @1
    wf
    cz
    cc
    wss
    @29
    @1
    cV
    mzpf
    zsscn
    @0
    cz
    cc
    @1
    fss
    sylancl
    vx
    @0
    cc
    cA
    @1
    @1
    eqid
    fmpt
    sylibr
    #
    @28
    vx
    @0
    @11
    c1
    @27
    vx
    @0
    nfra1
    #
    @28
    vx
    cv
    @0
    wcel
    #
    wa
    cA
    @27
    vx
    @0
    rspa
    #
    exp0d
    mpteq2da
    syl
    @3
    cV
    cvv
    wcel
    c1
    cz
    wcel
    @26
    @2
    wcel
    @1
    cV
    cmzp
    elfvex
    1z
    vx
    c1
    cV
    mzpconstmpt
    sylancl
    eqeltrd
    @14
    cn0
    wcel
    #
    @3
    @17
    @21
    @34
    @3
    @17
    @21
    @34
    @3
    @17
    w3a
    #
    @20
    vx
    @0
    @15
    cA
    cmul
    co
    #
    cmpt
    #
    @2
    @35
    @28
    @34
    @20
    @37
    wceq
    @3
    @34
    @28
    @17
    @30
    3ad2ant2
    @34
    @3
    @17
    simp1
    @28
    @34
    wa
    #
    vx
    @0
    @19
    @36
    @28
    @34
    vx
    @31
    @34
    vx
    nfv
    nfan
    @38
    @32
    wa
    cA
    @14
    @28
    @32
    @27
    @34
    @33
    adantlr
    @28
    @34
    @32
    simplr
    expp1d
    mpteq2da
    syl2anc
    @35
    @17
    @3
    @37
    @2
    wcel
    @34
    @3
    @17
    simp3
    @34
    @3
    @17
    simp2
    vx
    @15
    cA
    cV
    mzpmulmpt
    syl2anc
    eqeltrd
    3exp
    a2d
    nn0ind
    impcom
end
