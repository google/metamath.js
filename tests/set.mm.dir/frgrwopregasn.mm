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
include "wi.mm"
include "snidg.mm"
include "adantr.mm"
include "wb.mm"
include "eleq2.mm"
include "adantl.mm"
include "mpbird.mm"
include "preq1.mm"
include "eleq1d.mm"
include "ralbidv.mm"
include "rspcv.mm"
include "syl.mm"
include "difeq2.mm"
include "syl5eq.mm"
include "raleqdv.mm"
include "sylibd.mm"
include "syl5com.mm"
include "3impib.mm"

theorem frgrwopregasn
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
  assert |- ( ( G e. FriendGraph /\ X e. V /\ A = { X } ) -> A. w e. ( V \ { X } ) { X , w } e. E )

  proof
    cG
    cfrgr
    wcel
    #
    cX
    cV
    wcel
    #
    cA
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
    vv
    cv
    #
    @4
    cpr
    #
    cE
    wcel
    #
    vw
    cB
    wral
    #
    vv
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
    vv
    vw
    frgrwopreg.v
    frgrwopreg.d
    frgrwopreg.a
    frgrwopreg.b
    frgrwopreg.e
    frgrwopreglem4
    @14
    @13
    @6
    vw
    cB
    wral
    #
    @8
    @14
    cX
    cA
    wcel
    #
    @13
    @15
    wi
    @14
    @16
    cX
    @2
    wcel
    #
    @1
    @17
    @3
    cX
    cV
    snidg
    adantr
    @3
    @16
    @17
    wb
    @1
    cA
    @2
    cX
    eleq2
    adantl
    mpbird
    @12
    @15
    vv
    cX
    cA
    @9
    cX
    wceq
    #
    @11
    @6
    vw
    cB
    @18
    @10
    @5
    cE
    @9
    cX
    @4
    preq1
    eleq1d
    ralbidv
    rspcv
    syl
    @14
    @6
    vw
    cB
    @7
    @3
    cB
    @7
    wceq
    @1
    @3
    cB
    cV
    cA
    cdif
    @7
    frgrwopreg.b
    cA
    @2
    cV
    difeq2
    syl5eq
    adantl
    raleqdv
    sylibd
    syl5com
    3impib
end
