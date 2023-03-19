include "cr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "cneg.mm"
include "wceq.mm"
include "cab.mm"
include "wcel.mm"
include "renegcld.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimiv.mm"
include "abssi.mm"
include "eqsstri.mm"
include "csb.mm"
include "eqid.mm"
include "nfth.mm"
include "csbeq1a.mm"
include "negeqd.mm"
include "eqeq2d.mm"
include "rspce.mm"
include "mp2an.mm"
include "negex.mm"
include "nfcsb1v.mm"
include "nfneg.mm"
include "nfeq2.mm"
include "eqeq1.mm"
include "rexbid.mm"
include "elab.mm"
include "mpbir.mm"
include "eleqtrri.mm"
include "ne0ii.mm"
include "3pm3.2i.mm"

theorem infcvgaux1i
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cR: class R
  let cX: class X
  let cZ: class Z
  let cB: class B
  let cC: class C
  assume infcvg.1: |- R = { x | E. y e. X x = -u A }
  assume infcvg.2: |- ( y e. X -> A e. RR )
  assume infcvg.3: |- Z e. X
  assume infcvg.4: |- E. z e. RR A. w e. R w <_ z

  disjoint A x
  disjoint x y
  disjoint w z
  disjoint R w
  disjoint R z
  disjoint X x
  disjoint X y
  disjoint Z x
  disjoint Z y
  disjoint B x
  disjoint B y
  disjoint C y
  assert |- ( R C_ RR /\ R =/= (/) /\ E. z e. RR A. w e. R w <_ z )

  proof
    cR
    cr
    wss
    cR
    c0
    wne
    vw
    cv
    vz
    cv
    cle
    wbr
    vw
    cR
    wral
    vz
    cr
    wrex
    cR
    vx
    cv
    #
    cA
    cneg
    #
    wceq
    #
    vy
    cX
    wrex
    #
    vx
    cab
    #
    cr
    infcvg.1
    @3
    vx
    cr
    @2
    @0
    cr
    wcel
    #
    vy
    cX
    vy
    cv
    #
    cX
    wcel
    #
    @5
    @2
    @1
    cr
    wcel
    @7
    cA
    infcvg.2
    renegcld
    @0
    @1
    cr
    eleq1
    syl5ibrcom
    rexlimiv
    abssi
    eqsstri
    vy
    cZ
    cA
    csb
    #
    cneg
    #
    cR
    @9
    @4
    cR
    @9
    @4
    wcel
    @9
    @1
    wceq
    #
    vy
    cX
    wrex
    #
    cZ
    cX
    wcel
    @9
    @9
    wceq
    #
    @11
    infcvg.3
    @9
    eqid
    #
    @10
    @12
    vy
    cZ
    cX
    @12
    vy
    @13
    nfth
    @6
    cZ
    wceq
    #
    @1
    @9
    @9
    @14
    cA
    @8
    vy
    cZ
    cA
    csbeq1a
    negeqd
    eqeq2d
    rspce
    mp2an
    @3
    @11
    vx
    @9
    @8
    negex
    @0
    @9
    wceq
    @2
    @10
    vy
    cX
    vy
    @0
    @9
    vy
    @8
    vy
    cZ
    cA
    nfcsb1v
    nfneg
    nfeq2
    @0
    @9
    @1
    eqeq1
    rexbid
    elab
    mpbir
    infcvg.1
    eleqtrri
    ne0ii
    infcvg.4
    3pm3.2i
end
