include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "cvv.mm"
include "cmeas.mm"
include "cfv.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
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
include "elex.mm"
include "a1i.mm"
include "simp1.mm"
include "ovex.mm"
include "fex2.mm"
include "3expb.mm"
include "expcom.mm"
include "mpan2.mm"
include "syl5.mm"
include "wb.mm"
include "df-meas.mm"
include "cab.mm"
include "vex.mm"
include "mapex.mm"
include "mp2an.mm"
include "ss2abi.mm"
include "ssexi.mm"
include "simpr.mm"
include "simpl.mm"
include "feq12d.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "adantl.mm"
include "pweqd.mm"
include "esumeq2sdv.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "raleqbidv.mm"
include "3anbi123d.mm"
include "abfmpel.mm"
include "ex.mm"
include "pm5.21ndd.mm"

theorem ismeas
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cM: class M
  let vm: setvar m
  let vs: setvar s

  disjoint x y
  disjoint M x
  disjoint M y
  disjoint S x
  disjoint m x
  disjoint s x
  disjoint m y
  disjoint s y
  disjoint m s
  disjoint M m
  disjoint M s
  disjoint S m
  disjoint S s
  assert |- ( S e. U. ran sigAlgebra -> ( M e. ( measures ` S ) <-> ( M : S --> ( 0 [,] +oo ) /\ ( M ` (/) ) = 0 /\ A. x e. ~P S ( ( x ~<_ _om /\ Disj_ y e. x y ) -> ( M ` U. x ) = sum* y e. x ( M ` y ) ) ) ) )

  proof
    cS
    csiga
    crn
    cuni
    #
    wcel
    #
    cM
    cvv
    wcel
    #
    cM
    cS
    cmeas
    cfv
    #
    wcel
    #
    cS
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
    @9
    vy
    cv
    #
    wdisj
    wa
    #
    @9
    cuni
    #
    cM
    cfv
    #
    @9
    @10
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
    cS
    cpw
    #
    wral
    #
    w3a
    #
    @4
    @2
    wi
    @1
    cM
    @3
    elex
    a1i
    @20
    @6
    @1
    @2
    @6
    @8
    @19
    simp1
    @1
    @5
    cvv
    wcel
    #
    @6
    @2
    wi
    cc0
    cpnf
    cicc
    ovex
    #
    @6
    @1
    @21
    wa
    @2
    @6
    @1
    @21
    @2
    cS
    @5
    cM
    @0
    cvv
    fex2
    3expb
    expcom
    mpan2
    syl5
    @1
    @2
    @4
    @20
    wb
    vs
    cv
    #
    @5
    vm
    cv
    #
    wf
    #
    c0
    @24
    cfv
    #
    cc0
    wceq
    #
    @11
    @12
    @24
    cfv
    #
    @9
    @10
    @24
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
    @23
    cpw
    #
    wral
    #
    w3a
    #
    @20
    vs
    vm
    cS
    cM
    cmeas
    @0
    cvv
    vx
    vy
    vm
    vs
    df-meas
    @35
    vm
    cab
    @25
    vm
    cab
    #
    @23
    cvv
    wcel
    @21
    @36
    cvv
    wcel
    vs
    vex
    @22
    @23
    @5
    cvv
    cvv
    vm
    mapex
    mp2an
    @35
    @25
    vm
    @25
    @27
    @34
    simp1
    ss2abi
    ssexi
    @23
    cS
    wceq
    #
    @24
    cM
    wceq
    #
    wa
    #
    @25
    @6
    @27
    @8
    @34
    @19
    @39
    @23
    cS
    @5
    @24
    cM
    @37
    @38
    simpr
    @37
    @38
    simpl
    #
    feq12d
    @38
    @27
    @8
    wb
    @37
    @38
    @26
    @7
    cc0
    c0
    @24
    cM
    fveq1
    eqeq1d
    adantl
    @39
    @32
    @17
    vx
    @33
    @18
    @39
    @23
    cS
    @40
    pweqd
    @38
    @32
    @17
    wb
    @37
    @38
    @31
    @16
    @11
    @38
    @28
    @13
    @30
    @15
    @12
    @24
    cM
    fveq1
    @38
    @9
    @29
    @14
    vy
    @10
    @24
    cM
    fveq1
    esumeq2sdv
    eqeq12d
    imbi2d
    adantl
    raleqbidv
    3anbi123d
    abfmpel
    ex
    pm5.21ndd
end
