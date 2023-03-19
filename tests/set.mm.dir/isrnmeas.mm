include "cmeas.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "cv.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "c0.mm"
include "cfv.mm"
include "wceq.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wdisj.mm"
include "wa.mm"
include "cesum.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "w3a.mm"
include "csiga.mm"
include "wrex.mm"
include "cdm.mm"
include "cvv.mm"
include "df-meas.mm"
include "cab.mm"
include "vex.mm"
include "ovex.mm"
include "mapex.mm"
include "mp2an.mm"
include "simp1.mm"
include "ss2abi.mm"
include "ssexi.mm"
include "feq1.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "esumeq2sdv.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "3anbi123d.mm"
include "abfmpunirn.mm"
include "simprbi.mm"
include "fdm.mm"
include "3ad2ant1.mm"
include "adantl.mm"
include "simpl.mm"
include "eqeltrd.mm"
include "feq2.mm"
include "biimpar.mm"
include "syl2anc.mm"
include "simp2.mm"
include "simp3.mm"
include "pweq.mm"
include "raleqdv.mm"
include "3jca.mm"
include "jca.mm"
include "rexlimiva.mm"
include "syl.mm"

theorem isrnmeas
  let vx: setvar x
  let vy: setvar y
  let cM: class M
  let vm: setvar m
  let vs: setvar s

  disjoint x y
  disjoint M x
  disjoint M y
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint M m
  disjoint s x
  disjoint s y
  disjoint M s
  assert |- ( M e. U. ran measures -> ( dom M e. U. ran sigAlgebra /\ ( M : dom M --> ( 0 [,] +oo ) /\ ( M ` (/) ) = 0 /\ A. x e. ~P dom M ( ( x ~<_ _om /\ Disj_ y e. x y ) -> ( M ` U. x ) = sum* y e. x ( M ` y ) ) ) ) )

  proof
    cM
    cmeas
    crn
    cuni
    wcel
    #
    vs
    cv
    #
    cc0
    cpnf
    cicc
    co
    #
    cM
    wf
    #
    c0
    cM
    cfv
    #
    cc0
    wceq
    #
    vx
    cv
    #
    com
    cdom
    wbr
    vy
    @6
    vy
    cv
    #
    wdisj
    wa
    #
    @6
    cuni
    #
    cM
    cfv
    #
    @6
    @7
    cM
    cfv
    #
    vy
    cesum
    #
    wceq
    #
    wi
    #
    vx
    @1
    cpw
    #
    wral
    #
    w3a
    #
    vs
    csiga
    crn
    cuni
    #
    wrex
    #
    cM
    cdm
    #
    @18
    wcel
    #
    @20
    @2
    cM
    wf
    #
    @5
    @14
    vx
    @20
    cpw
    #
    wral
    #
    w3a
    #
    wa
    #
    @0
    cM
    cvv
    wcel
    @19
    @1
    @2
    vm
    cv
    #
    wf
    #
    c0
    @27
    cfv
    #
    cc0
    wceq
    #
    @8
    @9
    @27
    cfv
    #
    @6
    @7
    @27
    cfv
    #
    vy
    cesum
    #
    wceq
    #
    wi
    #
    vx
    @15
    wral
    #
    w3a
    #
    @17
    vs
    vm
    cM
    cmeas
    @18
    vx
    vy
    vm
    vs
    df-meas
    @37
    vm
    cab
    @28
    vm
    cab
    #
    @1
    cvv
    wcel
    @2
    cvv
    wcel
    @38
    cvv
    wcel
    vs
    vex
    cc0
    cpnf
    cicc
    ovex
    @1
    @2
    cvv
    cvv
    vm
    mapex
    mp2an
    @37
    @28
    vm
    @28
    @30
    @36
    simp1
    ss2abi
    ssexi
    @27
    cM
    wceq
    #
    @28
    @3
    @30
    @5
    @36
    @16
    @1
    @2
    @27
    cM
    feq1
    @39
    @29
    @4
    cc0
    c0
    @27
    cM
    fveq1
    eqeq1d
    @39
    @35
    @14
    vx
    @15
    @39
    @34
    @13
    @8
    @39
    @31
    @10
    @33
    @12
    @9
    @27
    cM
    fveq1
    @39
    @6
    @32
    @11
    vy
    @7
    @27
    cM
    fveq1
    esumeq2sdv
    eqeq12d
    imbi2d
    ralbidv
    3anbi123d
    abfmpunirn
    simprbi
    @17
    @26
    vs
    @18
    @1
    @18
    wcel
    #
    @17
    wa
    #
    @21
    @25
    @41
    @20
    @1
    @18
    @17
    @20
    @1
    wceq
    #
    @40
    @3
    @5
    @42
    @16
    @1
    @2
    cM
    fdm
    3ad2ant1
    #
    adantl
    @40
    @17
    simpl
    eqeltrd
    @17
    @25
    @40
    @17
    @22
    @5
    @24
    @17
    @42
    @3
    @22
    @43
    @3
    @5
    @16
    simp1
    @42
    @22
    @3
    @20
    @1
    @2
    cM
    feq2
    biimpar
    syl2anc
    @3
    @5
    @16
    simp2
    @17
    @42
    @16
    @24
    @43
    @3
    @5
    @16
    simp3
    @42
    @24
    @16
    @42
    @14
    vx
    @23
    @15
    @20
    @1
    pweq
    raleqdv
    biimpar
    syl2anc
    3jca
    adantl
    jca
    rexlimiva
    syl
end
