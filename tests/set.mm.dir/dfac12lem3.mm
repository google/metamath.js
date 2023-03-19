include "cr1.mm"
include "cfv.mm"
include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "crn.mm"
include "cvv.mm"
include "con0.mm"
include "wss.mm"
include "fvex.mm"
include "rnex.mm"
include "wf1.mm"
include "wf.mm"
include "ssid.mm"
include "wi.mm"
include "cv.mm"
include "wceq.mm"
include "sseq1.mm"
include "wb.mm"
include "fveq2.mm"
include "f1eq1.mm"
include "syl.mm"
include "f1eq2.mm"
include "bitrd.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "wral.mm"
include "r19.21v.mm"
include "wa.mm"
include "word.mm"
include "eloni.mm"
include "ad2antrl.mm"
include "ordelss.mm"
include "sylan.mm"
include "simplrr.mm"
include "sstrd.mm"
include "pm5.5.mm"
include "ralbidva.mm"
include "cuni.mm"
include "cep.mm"
include "coi.mm"
include "ccnv.mm"
include "ccom.mm"
include "ad2antrr.mm"
include "char.mm"
include "cpw.mm"
include "simplrl.mm"
include "eqid.mm"
include "simpr.mm"
include "cbvralv.mm"
include "sylib.mm"
include "dfac12lem2.mm"
include "ex.mm"
include "sylbid.mm"
include "expr.mm"
include "com23.mm"
include "expcom.mm"
include "a2d.mm"
include "syl5bi.mm"
include "tfis3.mm"
include "mpcom.mm"
include "mpi.mm"
include "f1f.mm"
include "frn.mm"
include "3syl.mm"
include "onssnum.mm"
include "sylancr.mm"
include "wf1o.mm"
include "cen.mm"
include "wbr.mm"
include "f1f1orn.mm"
include "f1oen.mm"
include "ennum.mm"
include "mpbird.mm"

theorem dfac12lem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let cG: class G
  let vm: setvar m
  let vn: setvar n
  let vz: setvar z
  let cC: class C
  let cH: class H
  assume dfac12.1: |- ( ph -> A e. On )
  assume dfac12.3: |- ( ph -> F : ~P ( har ` ( R1 ` A ) ) -1-1-> On )
  assume dfac12.4: |- G = recs ( ( x e. _V |-> ( y e. ( R1 ` dom x ) |-> if ( dom x = U. dom x , ( ( suc U. ran U. ran x .o ( rank ` y ) ) +o ( ( x ` suc ( rank ` y ) ) ` y ) ) , ( F ` ( ( `' OrdIso ( _E , ran ( x ` U. dom x ) ) o. ( x ` U. dom x ) ) " y ) ) ) ) ) )

  disjoint A y
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint ph y
  disjoint F x
  disjoint F y
  disjoint m n
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint y z
  disjoint A z
  disjoint x z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint m x
  disjoint G m
  disjoint n x
  disjoint G n
  disjoint G z
  disjoint m ph
  disjoint n ph
  disjoint ph z
  disjoint F z
  disjoint H y
  disjoint H z
  assert |- ( ph -> ( R1 ` A ) e. dom card )

  proof
    wph
    cA
    cr1
    cfv
    #
    ccrd
    cdm
    #
    wcel
    #
    cA
    cG
    cfv
    #
    crn
    #
    @1
    wcel
    #
    wph
    @4
    cvv
    wcel
    @4
    con0
    wss
    #
    @5
    @3
    cA
    cG
    fvex
    rnex
    wph
    @0
    con0
    @3
    wf1
    #
    @0
    con0
    @3
    wf
    @6
    wph
    cA
    cA
    wss
    #
    @7
    cA
    ssid
    cA
    con0
    wcel
    #
    wph
    @8
    @7
    wi
    #
    dfac12.1
    wph
    vm
    cv
    #
    cA
    wss
    #
    @11
    cr1
    cfv
    #
    con0
    @11
    cG
    cfv
    #
    wf1
    #
    wi
    #
    wi
    #
    wph
    vn
    cv
    #
    cA
    wss
    #
    @18
    cr1
    cfv
    #
    con0
    @18
    cG
    cfv
    #
    wf1
    #
    wi
    #
    wi
    #
    wph
    @10
    wi
    vm
    vn
    cA
    @11
    @18
    wceq
    #
    @16
    @23
    wph
    @25
    @12
    @19
    @15
    @22
    @11
    @18
    cA
    sseq1
    @25
    @15
    @13
    con0
    @21
    wf1
    #
    @22
    @25
    @14
    @21
    wceq
    @15
    @26
    wb
    @11
    @18
    cG
    fveq2
    @13
    con0
    @14
    @21
    f1eq1
    syl
    @25
    @13
    @20
    wceq
    @26
    @22
    wb
    @11
    @18
    cr1
    fveq2
    @13
    @20
    con0
    @21
    f1eq2
    syl
    bitrd
    imbi12d
    imbi2d
    @11
    cA
    wceq
    #
    @16
    @10
    wph
    @27
    @12
    @8
    @15
    @7
    @11
    cA
    cA
    sseq1
    @27
    @15
    @13
    con0
    @3
    wf1
    #
    @7
    @27
    @14
    @3
    wceq
    @15
    @28
    wb
    @11
    cA
    cG
    fveq2
    @13
    con0
    @14
    @3
    f1eq1
    syl
    @27
    @13
    @0
    wceq
    @28
    @7
    wb
    @11
    cA
    cr1
    fveq2
    @13
    @0
    con0
    @3
    f1eq2
    syl
    bitrd
    imbi12d
    imbi2d
    @24
    vn
    @11
    wral
    wph
    @23
    vn
    @11
    wral
    #
    wi
    @11
    con0
    wcel
    #
    @17
    wph
    @23
    vn
    @11
    r19.21v
    @30
    wph
    @29
    @16
    wph
    @30
    @29
    @16
    wi
    wph
    @30
    wa
    @12
    @29
    @15
    wph
    @30
    @12
    @29
    @15
    wi
    wph
    @30
    @12
    wa
    #
    wa
    #
    @29
    @22
    vn
    @11
    wral
    #
    @15
    @32
    @23
    @22
    vn
    @11
    @32
    @18
    @11
    wcel
    #
    wa
    #
    @19
    @23
    @22
    wb
    @35
    @18
    @11
    cA
    @32
    @11
    word
    #
    @34
    @18
    @11
    wss
    @30
    @36
    wph
    @12
    @11
    eloni
    ad2antrl
    @11
    @18
    ordelss
    sylan
    wph
    @30
    @12
    @34
    simplrr
    sstrd
    @19
    @22
    pm5.5
    syl
    ralbidva
    @32
    @33
    @15
    @32
    @33
    wa
    #
    vx
    vy
    vz
    cA
    @11
    cF
    cG
    @11
    cuni
    cG
    cfv
    #
    crn
    cep
    coi
    ccnv
    @38
    ccom
    #
    wph
    @9
    @31
    @33
    dfac12.1
    ad2antrr
    wph
    @0
    char
    cfv
    cpw
    con0
    cF
    wf1
    @31
    @33
    dfac12.3
    ad2antrr
    dfac12.4
    wph
    @30
    @12
    @33
    simplrl
    @39
    eqid
    wph
    @30
    @12
    @33
    simplrr
    @37
    @33
    vz
    cv
    #
    cr1
    cfv
    #
    con0
    @40
    cG
    cfv
    #
    wf1
    #
    vz
    @11
    wral
    @32
    @33
    simpr
    @22
    @43
    vn
    vz
    @11
    @18
    @40
    wceq
    #
    @22
    @20
    con0
    @42
    wf1
    #
    @43
    @44
    @21
    @42
    wceq
    @22
    @45
    wb
    @18
    @40
    cG
    fveq2
    @20
    con0
    @21
    @42
    f1eq1
    syl
    @44
    @20
    @41
    wceq
    @45
    @43
    wb
    @18
    @40
    cr1
    fveq2
    @20
    @41
    con0
    @42
    f1eq2
    syl
    bitrd
    cbvralv
    sylib
    dfac12lem2
    ex
    sylbid
    expr
    com23
    expcom
    a2d
    syl5bi
    tfis3
    mpcom
    mpi
    #
    @0
    con0
    @3
    f1f
    @0
    con0
    @3
    frn
    3syl
    @4
    cvv
    onssnum
    sylancr
    wph
    @0
    @4
    @3
    wf1o
    #
    @0
    @4
    cen
    wbr
    @2
    @5
    wb
    wph
    @7
    @47
    @46
    @0
    con0
    @3
    f1f1orn
    syl
    @0
    @4
    @3
    cA
    cr1
    fvex
    f1oen
    @0
    @4
    ennum
    3syl
    mpbird
end
