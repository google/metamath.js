include "cv.mm"
include "cdm.mm"
include "cr1.mm"
include "cfv.mm"
include "cvv.mm"
include "crn.mm"
include "cdif.mm"
include "cmpt.mm"
include "crecs.mm"
include "wceq.mm"
include "weq.mm"
include "rneq.mm"
include "difeq2d.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "recseq.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "fvexd.mm"
include "c0.mm"
include "wne.mm"
include "wcel.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "aomclem2.mm"
include "neeq1.mm"
include "fveq2.mm"
include "id.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "sylib.mm"
include "dnwech.mm"

theorem aomclem3
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume aomclem3.b: |- B = { <. a , b >. | E. c e. ( R1 ` U. dom z ) ( ( c e. b /\ -. c e. a ) /\ A. d e. ( R1 ` U. dom z ) ( d ( z ` U. dom z ) c -> ( d e. a <-> d e. b ) ) ) }
  assume aomclem3.c: |- C = ( a e. _V |-> sup ( ( y ` a ) , ( R1 ` dom z ) , B ) )
  assume aomclem3.d: |- D = recs ( ( a e. _V |-> ( C ` ( ( R1 ` dom z ) \ ran a ) ) ) )
  assume aomclem3.e: |- E = { <. a , b >. | |^| ( `' D " { a } ) e. |^| ( `' D " { b } ) }
  assume aomclem3.on: |- ( ph -> dom z e. On )
  assume aomclem3.su: |- ( ph -> dom z = suc U. dom z )
  assume aomclem3.we: |- ( ph -> A. a e. dom z ( z ` a ) We ( R1 ` a ) )
  assume aomclem3.a: |- ( ph -> A e. On )
  assume aomclem3.za: |- ( ph -> dom z C_ A )
  assume aomclem3.y: |- ( ph -> A. a e. ~P ( R1 ` A ) ( a =/= (/) -> ( y ` a ) e. ( ( ~P a i^i Fin ) \ { (/) } ) ) )

  disjoint y z
  disjoint a z
  disjoint b z
  disjoint c z
  disjoint d z
  disjoint a y
  disjoint b y
  disjoint c y
  disjoint d y
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint b c
  disjoint b d
  disjoint c d
  disjoint a ph
  disjoint b ph
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C d
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D d
  assert |- ( ph -> E We ( R1 ` dom z ) )

  proof
    wph
    vd
    vc
    vb
    va
    vz
    cv
    cdm
    #
    cr1
    cfv
    #
    cD
    cC
    cE
    cvv
    cD
    va
    cvv
    @1
    va
    cv
    #
    crn
    #
    cdif
    #
    cC
    cfv
    #
    cmpt
    #
    crecs
    #
    vc
    cvv
    @1
    vc
    cv
    #
    crn
    #
    cdif
    #
    cC
    cfv
    #
    cmpt
    #
    crecs
    #
    aomclem3.d
    @6
    @12
    wceq
    @7
    @13
    wceq
    va
    vc
    cvv
    @5
    @11
    va
    vc
    weq
    #
    @4
    @10
    cC
    @14
    @3
    @9
    @1
    @2
    @8
    rneq
    difeq2d
    fveq2d
    cbvmptv
    @6
    @12
    recseq
    ax-mp
    eqtri
    wph
    @0
    cr1
    fvexd
    wph
    @2
    c0
    wne
    #
    @2
    cC
    cfv
    #
    @2
    wcel
    #
    wi
    #
    va
    @1
    cpw
    #
    wral
    vd
    cv
    #
    c0
    wne
    #
    @20
    cC
    cfv
    #
    @20
    wcel
    #
    wi
    #
    vd
    @19
    wral
    wph
    vy
    vz
    cA
    cB
    cC
    va
    vb
    vc
    vd
    aomclem3.b
    aomclem3.c
    aomclem3.on
    aomclem3.su
    aomclem3.we
    aomclem3.a
    aomclem3.za
    aomclem3.y
    aomclem2
    @18
    @24
    va
    vd
    @19
    va
    vd
    weq
    #
    @15
    @21
    @17
    @23
    @2
    @20
    c0
    neeq1
    @25
    @16
    @22
    @2
    @20
    @2
    @20
    cC
    fveq2
    @25
    id
    eleq12d
    imbi12d
    cbvralv
    sylib
    aomclem3.e
    dnwech
end
