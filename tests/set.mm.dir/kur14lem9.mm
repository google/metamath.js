include "c1.mm"
include "c4.mm"
include "cdc.mm"
include "cv.mm"
include "wcel.mm"
include "cdif.mm"
include "cfv.mm"
include "cpr.mm"
include "wss.mm"
include "wral.mm"
include "wa.mm"
include "cpw.mm"
include "crab.mm"
include "cint.mm"
include "wi.mm"
include "vex.mm"
include "elintrab.mm"
include "ctp.mm"
include "cun.mm"
include "ssun1.mm"
include "sseqtr4i.mm"
include "sstri.mm"
include "ctop.mm"
include "topopn.mm"
include "ax-mp.mm"
include "elexi.mm"
include "ssexi.mm"
include "tpid1.mm"
include "sselii.mm"
include "kur14lem7.mm"
include "simprd.mm"
include "rgen.mm"
include "simpld.mm"
include "elpw2.mm"
include "sylibr.mm"
include "ssriv.mm"
include "pwex.mm"
include "mpbir.mm"
include "wceq.mm"
include "eleq2.mm"
include "sseq2.mm"
include "raleqbi1dv.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "rspccv.mm"
include "mpi.mm"
include "mp2ani.mm"
include "sylbi.mm"
include "eqsstri.mm"
include "kur14lem8.mm"
include "1nn0.mm"
include "4nn0.mm"
include "deccl.mm"
include "hashsslei.mm"

theorem kur14lem9
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let cI: class I
  let cJ: class J
  let cK: class K
  let cX: class X
  let vs: setvar s
  assume kur14lem.j: |- J e. Top
  assume kur14lem.x: |- X = U. J
  assume kur14lem.k: |- K = ( cls ` J )
  assume kur14lem.i: |- I = ( int ` J )
  assume kur14lem.a: |- A C_ X
  assume kur14lem.b: |- B = ( X \ ( K ` A ) )
  assume kur14lem.c: |- C = ( K ` ( X \ A ) )
  assume kur14lem.d: |- D = ( I ` ( K ` A ) )
  assume kur14lem.t: |- T = ( ( ( { A , ( X \ A ) , ( K ` A ) } u. { B , C , ( I ` A ) } ) u. { ( K ` B ) , D , ( K ` ( I ` A ) ) } ) u. ( { ( I ` C ) , ( K ` D ) , ( I ` ( K ` B ) ) } u. { ( K ` ( I ` C ) ) , ( I ` ( K ` ( I ` A ) ) ) } ) )
  assume kur14lem.s: |- S = |^| { x e. ~P ~P X | ( A e. x /\ A. y e. x { ( X \ y ) , ( K ` y ) } C_ x ) }

  disjoint A x
  disjoint K x
  disjoint x y
  disjoint T x
  disjoint T y
  disjoint X x
  disjoint X y
  disjoint s x
  disjoint A s
  disjoint K s
  disjoint s y
  disjoint T s
  disjoint X s
  assert |- ( S e. Fin /\ ( # ` S ) <_ ; 1 4 )

  proof
    cT
    cS
    c1
    c4
    cdc
    cS
    cA
    vx
    cv
    #
    wcel
    #
    cX
    vy
    cv
    #
    cdif
    @2
    cK
    cfv
    cpr
    #
    @0
    wss
    #
    vy
    @0
    wral
    #
    wa
    #
    vx
    cX
    cpw
    #
    cpw
    #
    crab
    cint
    #
    cT
    kur14lem.s
    vs
    @9
    cT
    vs
    cv
    #
    @9
    wcel
    @6
    @10
    @0
    wcel
    #
    wi
    #
    vx
    @8
    wral
    #
    @10
    cT
    wcel
    #
    @6
    vx
    @10
    @8
    vs
    vex
    elintrab
    @13
    cA
    cT
    wcel
    #
    @3
    cT
    wss
    #
    vy
    cT
    wral
    #
    @14
    cA
    cX
    cA
    cdif
    #
    cA
    cK
    cfv
    #
    ctp
    #
    cT
    cA
    @20
    @20
    cB
    cC
    cA
    cI
    cfv
    #
    ctp
    #
    cun
    #
    cT
    @20
    @22
    ssun1
    @23
    @23
    cB
    cK
    cfv
    #
    cD
    @21
    cK
    cfv
    #
    ctp
    #
    cun
    #
    cT
    @23
    @26
    ssun1
    @27
    @27
    cC
    cI
    cfv
    #
    cD
    cK
    cfv
    @24
    cI
    cfv
    ctp
    @28
    cK
    cfv
    @25
    cI
    cfv
    cpr
    cun
    #
    cun
    cT
    @27
    @29
    ssun1
    kur14lem.t
    sseqtr4i
    sstri
    sstri
    cA
    @18
    @19
    cA
    cX
    cX
    cJ
    cJ
    ctop
    wcel
    cX
    cJ
    wcel
    kur14lem.j
    cJ
    cX
    kur14lem.x
    topopn
    ax-mp
    elexi
    #
    kur14lem.a
    ssexi
    tpid1
    sselii
    @16
    vy
    cT
    @2
    cT
    wcel
    #
    @2
    cX
    wss
    #
    @16
    cA
    cB
    cC
    cD
    cT
    cI
    cJ
    cK
    @2
    cX
    kur14lem.j
    kur14lem.x
    kur14lem.k
    kur14lem.i
    kur14lem.a
    kur14lem.b
    kur14lem.c
    kur14lem.d
    kur14lem.t
    kur14lem7
    #
    simprd
    rgen
    @13
    cT
    @8
    wcel
    #
    @15
    @17
    wa
    #
    @14
    wi
    #
    @34
    cT
    @7
    wss
    vy
    cT
    @7
    @31
    @32
    @2
    @7
    wcel
    @31
    @32
    @16
    @33
    simpld
    @2
    cX
    @30
    elpw2
    sylibr
    ssriv
    cT
    @7
    cX
    @30
    pwex
    elpw2
    mpbir
    @12
    @36
    vx
    cT
    @8
    @0
    cT
    wceq
    #
    @6
    @35
    @11
    @14
    @37
    @1
    @15
    @5
    @17
    @0
    cT
    cA
    eleq2
    @4
    @16
    vy
    @0
    cT
    @0
    cT
    @3
    sseq2
    raleqbi1dv
    anbi12d
    @0
    cT
    @10
    eleq2
    imbi12d
    rspccv
    mpi
    mp2ani
    sylbi
    ssriv
    eqsstri
    cA
    cB
    cC
    cD
    cT
    cI
    cJ
    cK
    cX
    kur14lem.j
    kur14lem.x
    kur14lem.k
    kur14lem.i
    kur14lem.a
    kur14lem.b
    kur14lem.c
    kur14lem.d
    kur14lem.t
    kur14lem8
    c1
    c4
    1nn0
    4nn0
    deccl
    hashsslei
end
