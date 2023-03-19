include "com.mm"
include "crn.mm"
include "cuni.mm"
include "cxp.mm"
include "cpw.mm"
include "char.mm"
include "cfv.mm"
include "cr1.mm"
include "fvex.mm"
include "cv.mm"
include "wcel.mm"
include "crnk.mm"
include "hsmexlem5.mm"
include "con0.mm"
include "cima.mm"
include "cdm.mm"
include "wb.mm"
include "cdom.mm"
include "wbr.mm"
include "csn.mm"
include "ctc.mm"
include "wral.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseli.mm"
include "harcl.mm"
include "wfn.mm"
include "wceq.mm"
include "r1fnon.mm"
include "fndm.mm"
include "ax-mp.mm"
include "eleqtrri.mm"
include "rankr1ag.mm"
include "sylancl.mm"
include "mpbird.mm"
include "ssriv.mm"
include "ssexi.mm"

theorem hsmexlem6
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cS: class S
  let cU: class U
  let cH: class H
  let cO: class O
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  assume hsmexlem4.x: |- X e. _V
  assume hsmexlem4.h: |- H = ( rec ( ( z e. _V |-> ( har ` ~P ( X X. z ) ) ) , ( har ` ~P X ) ) |` _om )
  assume hsmexlem4.u: |- U = ( x e. _V |-> ( rec ( ( y e. _V |-> U. y ) , x ) |` _om ) )
  assume hsmexlem4.s: |- S = { a e. U. ( R1 " On ) | A. b e. ( TC ` { a } ) b ~<_ X }
  assume hsmexlem4.o: |- O = OrdIso ( _E , ( rank " ( ( U ` d ) ` c ) ) )

  disjoint a c
  disjoint a d
  disjoint H a
  disjoint c d
  disjoint H c
  disjoint H d
  disjoint S c
  disjoint S d
  disjoint U c
  disjoint U d
  disjoint a b
  disjoint a z
  disjoint X a
  disjoint b z
  disjoint X b
  disjoint X z
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b d
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint a e
  disjoint a f
  disjoint c e
  disjoint c f
  disjoint d e
  disjoint d f
  disjoint e f
  disjoint H e
  disjoint H f
  disjoint O e
  disjoint S e
  disjoint S f
  disjoint U f
  disjoint b e
  disjoint b f
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint f x
  disjoint f y
  disjoint f z
  assert |- S e. _V

  proof
    cS
    com
    cH
    crn
    cuni
    cxp
    cpw
    #
    char
    cfv
    #
    cr1
    cfv
    #
    @1
    cr1
    fvex
    vd
    cS
    @2
    vd
    cv
    #
    cS
    wcel
    #
    @3
    @2
    wcel
    #
    @3
    crnk
    cfv
    @1
    wcel
    #
    vx
    vy
    vz
    cS
    cU
    cH
    cO
    cX
    va
    vb
    vc
    vd
    hsmexlem4.x
    hsmexlem4.h
    hsmexlem4.u
    hsmexlem4.s
    hsmexlem4.o
    hsmexlem5
    @4
    @3
    cr1
    con0
    cima
    cuni
    #
    wcel
    @1
    cr1
    cdm
    #
    wcel
    @5
    @6
    wb
    cS
    @7
    @3
    cS
    vb
    cv
    cX
    cdom
    wbr
    vb
    va
    cv
    csn
    ctc
    cfv
    wral
    #
    va
    @7
    crab
    @7
    hsmexlem4.s
    @9
    va
    @7
    ssrab2
    eqsstri
    sseli
    @1
    con0
    @8
    @0
    harcl
    cr1
    con0
    wfn
    @8
    con0
    wceq
    r1fnon
    con0
    cr1
    fndm
    ax-mp
    eleqtrri
    @3
    @1
    rankr1ag
    sylancl
    mpbird
    ssriv
    ssexi
end
