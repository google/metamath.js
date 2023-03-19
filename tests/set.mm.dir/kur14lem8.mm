include "cdif.mm"
include "cfv.mm"
include "ctp.mm"
include "cun.mm"
include "cpr.mm"
include "c9.mm"
include "c5.mm"
include "c1.mm"
include "c4.mm"
include "cdc.mm"
include "c6.mm"
include "c3.mm"
include "eqid.mm"
include "hashtplei.mm"
include "3nn0.mm"
include "3p3e6.mm"
include "hashunlei.mm"
include "6nn0.mm"
include "6p3e9.mm"
include "c2.mm"
include "hashprlei.mm"
include "2nn0.mm"
include "3p2e5.mm"
include "9nn0.mm"
include "5nn0.mm"
include "9p5e14.mm"

theorem kur14lem8
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  let cI: class I
  let cJ: class J
  let cK: class K
  let cX: class X
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  assume kur14lem.j: |- J e. Top
  assume kur14lem.x: |- X = U. J
  assume kur14lem.k: |- K = ( cls ` J )
  assume kur14lem.i: |- I = ( int ` J )
  assume kur14lem.a: |- A C_ X
  assume kur14lem.b: |- B = ( X \ ( K ` A ) )
  assume kur14lem.c: |- C = ( K ` ( X \ A ) )
  assume kur14lem.d: |- D = ( I ` ( K ` A ) )
  assume kur14lem.t: |- T = ( ( ( { A , ( X \ A ) , ( K ` A ) } u. { B , C , ( I ` A ) } ) u. { ( K ` B ) , D , ( K ` ( I ` A ) ) } ) u. ( { ( I ` C ) , ( K ` D ) , ( I ` ( K ` B ) ) } u. { ( K ` ( I ` C ) ) , ( I ` ( K ` ( I ` A ) ) ) } ) )


  assert |- ( T e. Fin /\ ( # ` T ) <_ ; 1 4 )

  proof
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
    cB
    cK
    cfv
    #
    cD
    @3
    cK
    cfv
    #
    ctp
    #
    cun
    #
    cC
    cI
    cfv
    #
    cD
    cK
    cfv
    #
    @6
    cI
    cfv
    #
    ctp
    #
    @10
    cK
    cfv
    #
    @7
    cI
    cfv
    #
    cpr
    #
    cun
    #
    cT
    c9
    c5
    c1
    c4
    cdc
    kur14lem.t
    @5
    @8
    @9
    c6
    c3
    c9
    @9
    eqid
    @2
    @4
    @5
    c3
    c3
    c6
    @5
    eqid
    cA
    @0
    @1
    hashtplei
    cB
    cC
    @3
    hashtplei
    3nn0
    3nn0
    3p3e6
    hashunlei
    @6
    cD
    @7
    hashtplei
    6nn0
    3nn0
    6p3e9
    hashunlei
    @13
    @16
    @17
    c3
    c2
    c5
    @17
    eqid
    @10
    @11
    @12
    hashtplei
    @14
    @15
    hashprlei
    3nn0
    2nn0
    3p2e5
    hashunlei
    9nn0
    5nn0
    9p5e14
    hashunlei
end
