include "cv.mm"
include "cdm.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wf.mm"
include "wel.mm"
include "wss.mm"
include "cfv.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wceq.mm"
include "id.mm"
include "dmeq.mm"
include "pweqd.mm"
include "difeq1d.mm"
include "feq123d.mm"
include "fveq1.mm"
include "eleq2d.mm"
include "imbi2d.mm"
include "raleqbidv.mm"
include "anbi2d.mm"
include "anbi12d.mm"
include "elab2g.mm"

theorem gneispace2
  let cA: class A
  let vf: setvar f
  let vn: setvar n
  let cF: class F
  let cV: class V
  let vs: setvar s
  let vp: setvar p
  assume gneispace.a: |- A = { f | ( f : dom f --> ( ~P ( ~P dom f \ { (/) } ) \ { (/) } ) /\ A. p e. dom f A. n e. ( f ` p ) ( p e. n /\ A. s e. ~P dom f ( n C_ s -> s e. ( f ` p ) ) ) ) }

  disjoint F n
  disjoint F p
  disjoint n p
  disjoint F f
  disjoint F s
  disjoint f s
  disjoint f n
  disjoint f p
  assert |- ( F e. V -> ( F e. A <-> ( F : dom F --> ( ~P ( ~P dom F \ { (/) } ) \ { (/) } ) /\ A. p e. dom F A. n e. ( F ` p ) ( p e. n /\ A. s e. ~P dom F ( n C_ s -> s e. ( F ` p ) ) ) ) ) )

  proof
    vf
    cv
    #
    cdm
    #
    @1
    cpw
    #
    c0
    csn
    #
    cdif
    #
    cpw
    #
    @3
    cdif
    #
    @0
    wf
    #
    vp
    vn
    wel
    #
    vn
    cv
    vs
    cv
    #
    wss
    #
    @9
    vp
    cv
    #
    @0
    cfv
    #
    wcel
    #
    wi
    #
    vs
    @2
    wral
    #
    wa
    #
    vn
    @12
    wral
    #
    vp
    @1
    wral
    #
    wa
    cF
    cdm
    #
    @19
    cpw
    #
    @3
    cdif
    #
    cpw
    #
    @3
    cdif
    #
    cF
    wf
    #
    @8
    @10
    @9
    @11
    cF
    cfv
    #
    wcel
    #
    wi
    #
    vs
    @20
    wral
    #
    wa
    #
    vn
    @25
    wral
    #
    vp
    @19
    wral
    #
    wa
    vf
    cF
    cA
    cV
    @0
    cF
    wceq
    #
    @7
    @24
    @18
    @31
    @32
    @1
    @19
    @6
    @23
    @0
    cF
    @32
    id
    @0
    cF
    dmeq
    #
    @32
    @5
    @22
    @3
    @32
    @4
    @21
    @32
    @2
    @20
    @3
    @32
    @1
    @19
    @33
    pweqd
    #
    difeq1d
    pweqd
    difeq1d
    feq123d
    @32
    @17
    @30
    vp
    @1
    @19
    @33
    @32
    @16
    @29
    vn
    @12
    @25
    @11
    @0
    cF
    fveq1
    #
    @32
    @15
    @28
    @8
    @32
    @14
    @27
    vs
    @2
    @20
    @34
    @32
    @13
    @26
    @10
    @32
    @12
    @25
    @9
    @35
    eleq2d
    imbi2d
    raleqbidv
    anbi2d
    raleqbidv
    raleqbidv
    anbi12d
    gneispace.a
    elab2g
end
