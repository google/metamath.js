include "cfrgr.mm"
include "wcel.mm"
include "csn.mm"
include "wceq.mm"
include "cv.mm"
include "cpr.mm"
include "cdif.mm"
include "wral.mm"
include "wa.mm"
include "frgrwopreglem4.mm"
include "ralcom.mm"
include "wi.mm"
include "snidg.mm"
include "adantr.mm"
include "wb.mm"
include "eleq2.mm"
include "adantl.mm"
include "mpbird.mm"
include "preq2.mm"
include "prcom.mm"
include "syl6eq.mm"
include "eleq1d.mm"
include "ralbidv.mm"
include "rspcv.mm"
include "syl.mm"
include "wss.mm"
include "cfv.mm"
include "ssrab3.mm"
include "ssdifim.mm"
include "mp2an.mm"
include "difeq2.mm"
include "syl5eq.mm"
include "raleqdv.mm"
include "sylibd.mm"
include "syl5bi.mm"
include "syl5com.mm"
include "3impib.mm"

theorem frgrwopregbsn
  let vx: setvar x
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cD: class D
  let cE: class E
  let cG: class G
  let cK: class K
  let cV: class V
  let cX: class X
  let vb: setvar b
  let vy: setvar y
  let va: setvar a
  let vv: setvar v
  let cY: class Y
  assume frgrwopreg.v: |- V = ( Vtx ` G )
  assume frgrwopreg.d: |- D = ( VtxDeg ` G )
  assume frgrwopreg.a: |- A = { x e. V | ( D ` x ) = K }
  assume frgrwopreg.b: |- B = ( V \ A )
  assume frgrwopreg.e: |- E = ( Edg ` G )

  disjoint B x
  disjoint G x
  disjoint A w
  disjoint B w
  disjoint G w
  disjoint w x
  disjoint V w
  disjoint X w
  disjoint V x
  disjoint A x
  disjoint G x
  disjoint K x
  disjoint D x
  disjoint X x
  disjoint A b
  disjoint D y
  disjoint G a
  disjoint G b
  disjoint G y
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint x y
  disjoint V y
  disjoint A v
  disjoint v w
  disjoint B v
  disjoint E v
  disjoint G v
  disjoint v x
  disjoint X v
  disjoint Y x
  assert |- ( ( G e. FriendGraph /\ X e. V /\ B = { X } ) -> A. w e. ( V \ { X } ) { X , w } e. E )

  proof
    cG
    cfrgr
    wcel
    #
    cX
    cV
    wcel
    #
    cB
    cX
    csn
    #
    wceq
    #
    cX
    vw
    cv
    #
    cpr
    #
    cE
    wcel
    #
    vw
    cV
    @2
    cdif
    #
    wral
    #
    @0
    @4
    vv
    cv
    #
    cpr
    #
    cE
    wcel
    #
    vv
    cB
    wral
    vw
    cA
    wral
    #
    @1
    @3
    wa
    #
    @8
    vx
    cA
    cB
    cD
    cE
    cG
    cK
    cV
    vw
    vv
    frgrwopreg.v
    frgrwopreg.d
    frgrwopreg.a
    frgrwopreg.b
    frgrwopreg.e
    frgrwopreglem4
    @12
    @11
    vw
    cA
    wral
    #
    vv
    cB
    wral
    #
    @13
    @8
    @11
    vw
    vv
    cA
    cB
    ralcom
    @13
    @15
    @6
    vw
    cA
    wral
    #
    @8
    @13
    cX
    cB
    wcel
    #
    @15
    @16
    wi
    @13
    @17
    cX
    @2
    wcel
    #
    @1
    @18
    @3
    cX
    cV
    snidg
    adantr
    @3
    @17
    @18
    wb
    @1
    cB
    @2
    cX
    eleq2
    adantl
    mpbird
    @14
    @16
    vv
    cX
    cB
    @9
    cX
    wceq
    #
    @11
    @6
    vw
    cA
    @19
    @10
    @5
    cE
    @19
    @10
    @4
    cX
    cpr
    @5
    @9
    cX
    @4
    preq2
    @4
    cX
    prcom
    syl6eq
    eleq1d
    ralbidv
    rspcv
    syl
    @13
    @6
    vw
    cA
    @7
    @13
    cA
    cV
    cB
    cdif
    #
    @7
    cA
    cV
    wss
    cB
    cV
    cA
    cdif
    wceq
    cA
    @20
    wceq
    vx
    cv
    cD
    cfv
    cK
    wceq
    vx
    cV
    cA
    frgrwopreg.a
    ssrab3
    frgrwopreg.b
    cA
    cB
    cV
    ssdifim
    mp2an
    @3
    @20
    @7
    wceq
    @1
    cB
    @2
    cV
    difeq2
    adantl
    syl5eq
    raleqdv
    sylibd
    syl5bi
    syl5com
    3impib
end
