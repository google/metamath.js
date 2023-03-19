include "cfv.mm"
include "ccl.mm"
include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "cdif.mm"
include "difss.mm"
include "eqsstri.mm"
include "kur14lem3.mm"
include "cnt.mm"
include "fveq1i.mm"
include "ntrss2.mm"
include "mp2an.mm"
include "clsss.mm"
include "mp3an.mm"
include "3sstr4i.mm"
include "kur14lem5.mm"
include "sseqtri.mm"
include "kur14lem2.mm"
include "fveq2i.mm"
include "difeq2i.mm"
include "3eqtr2i.mm"
include "eqtr3i.mm"
include "sscon.mm"
include "ax-mp.mm"
include "eqssi.mm"

theorem kur14lem6
  let cA: class A
  let cB: class B
  let cI: class I
  let cJ: class J
  let cK: class K
  let cX: class X
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let cT: class T
  assume kur14lem.j: |- J e. Top
  assume kur14lem.x: |- X = U. J
  assume kur14lem.k: |- K = ( cls ` J )
  assume kur14lem.i: |- I = ( int ` J )
  assume kur14lem.a: |- A C_ X
  assume kur14lem.b: |- B = ( X \ ( K ` A ) )


  assert |- ( K ` ( I ` ( K ` B ) ) ) = ( K ` B )

  proof
    cB
    cK
    cfv
    #
    cI
    cfv
    #
    cK
    cfv
    #
    @0
    @2
    @0
    cK
    cfv
    #
    @0
    @1
    cJ
    ccl
    cfv
    #
    cfv
    #
    @0
    @4
    cfv
    #
    @2
    @3
    cJ
    ctop
    wcel
    #
    @0
    cX
    wss
    #
    @1
    @0
    wss
    @5
    @6
    wss
    kur14lem.j
    cB
    cI
    cJ
    cK
    cX
    kur14lem.j
    kur14lem.x
    kur14lem.k
    kur14lem.i
    cB
    cX
    cA
    cK
    cfv
    #
    cdif
    #
    cX
    kur14lem.b
    cX
    @9
    difss
    eqsstri
    #
    kur14lem3
    #
    @1
    @0
    cJ
    cnt
    cfv
    #
    cfv
    #
    @0
    @0
    cI
    @13
    kur14lem.i
    fveq1i
    @7
    @8
    @14
    @0
    wss
    kur14lem.j
    @12
    @0
    cJ
    cX
    kur14lem.x
    ntrss2
    mp2an
    eqsstri
    @0
    @1
    cJ
    cX
    kur14lem.x
    clsss
    mp3an
    @1
    cK
    @4
    kur14lem.k
    fveq1i
    #
    @0
    cK
    @4
    kur14lem.k
    fveq1i
    3sstr4i
    cB
    cI
    cJ
    cK
    cX
    kur14lem.j
    kur14lem.x
    kur14lem.k
    kur14lem.i
    @11
    kur14lem5
    sseqtri
    cB
    @4
    cfv
    #
    @5
    @0
    @2
    @7
    @1
    cX
    wss
    cB
    @1
    wss
    @16
    @5
    wss
    kur14lem.j
    @1
    cX
    cX
    @0
    cdif
    #
    cK
    cfv
    #
    cdif
    #
    cX
    @0
    cI
    cJ
    cK
    cX
    kur14lem.j
    kur14lem.x
    kur14lem.k
    kur14lem.i
    @12
    kur14lem2
    #
    cX
    @18
    difss
    eqsstri
    @10
    @19
    cB
    @1
    @18
    @9
    wss
    @10
    @19
    wss
    @17
    @4
    cfv
    #
    @9
    @4
    cfv
    #
    @18
    @9
    @7
    @9
    cX
    wss
    #
    @17
    @9
    wss
    @21
    @22
    wss
    kur14lem.j
    cA
    cI
    cJ
    cK
    cX
    kur14lem.j
    kur14lem.x
    kur14lem.k
    kur14lem.i
    kur14lem.a
    kur14lem3
    #
    @17
    @9
    @13
    cfv
    #
    @9
    @17
    cX
    @10
    cK
    cfv
    #
    cdif
    @9
    cI
    cfv
    @25
    @0
    @26
    cX
    cB
    @10
    cK
    kur14lem.b
    fveq2i
    difeq2i
    @9
    cI
    cJ
    cK
    cX
    kur14lem.j
    kur14lem.x
    kur14lem.k
    kur14lem.i
    @24
    kur14lem2
    @9
    cI
    @13
    kur14lem.i
    fveq1i
    3eqtr2i
    @7
    @23
    @25
    @9
    wss
    kur14lem.j
    @24
    @9
    cJ
    cX
    kur14lem.x
    ntrss2
    mp2an
    eqsstri
    @9
    @17
    cJ
    cX
    kur14lem.x
    clsss
    mp3an
    @17
    cK
    @4
    kur14lem.k
    fveq1i
    @9
    cK
    cfv
    @9
    @22
    cA
    cI
    cJ
    cK
    cX
    kur14lem.j
    kur14lem.x
    kur14lem.k
    kur14lem.i
    kur14lem.a
    kur14lem5
    @9
    cK
    @4
    kur14lem.k
    fveq1i
    eqtr3i
    3sstr4i
    @18
    @9
    cX
    sscon
    ax-mp
    kur14lem.b
    @20
    3sstr4i
    @1
    cB
    cJ
    cX
    kur14lem.x
    clsss
    mp3an
    cB
    cK
    @4
    kur14lem.k
    fveq1i
    @15
    3sstr4i
    eqssi
end
