include "c0.mm"
include "crdg.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "csuc.mm"
include "wceq.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "weq.mm"
include "com.mm"
include "wcel.mm"
include "ssid.mm"
include "a1i.mm"
include "wa.mm"
include "ackbij2lem3.mm"
include "ad2antrr.mm"
include "sstr2.mm"
include "syl5com.mm"
include "findsg.mm"

theorem ackbij2lem4
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cH: class H
  assume ackbij.f: |- F = ( x e. ( ~P _om i^i Fin ) |-> ( card ` U_ y e. x ( { y } X. ~P y ) ) )
  assume ackbij.g: |- G = ( x e. _V |-> ( y e. ~P dom x |-> ( F ` ( x " y ) ) ) )

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H x
  disjoint H y
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint B a
  disjoint B b
  disjoint B c
  assert |- ( ( ( A e. _om /\ B e. _om ) /\ B C_ A ) -> ( rec ( G , (/) ) ` B ) C_ ( rec ( G , (/) ) ` A ) )

  proof
    cB
    cG
    c0
    crdg
    #
    cfv
    #
    va
    cv
    #
    @0
    cfv
    #
    wss
    @1
    @1
    wss
    #
    @1
    vb
    cv
    #
    @0
    cfv
    #
    wss
    #
    @1
    @5
    csuc
    #
    @0
    cfv
    #
    wss
    #
    @1
    cA
    @0
    cfv
    #
    wss
    va
    vb
    cA
    cB
    @2
    cB
    wceq
    @3
    @1
    @1
    @2
    cB
    @0
    fveq2
    sseq2d
    va
    vb
    weq
    @3
    @6
    @1
    @2
    @5
    @0
    fveq2
    sseq2d
    @2
    @8
    wceq
    @3
    @9
    @1
    @2
    @8
    @0
    fveq2
    sseq2d
    @2
    cA
    wceq
    @3
    @11
    @1
    @2
    cA
    @0
    fveq2
    sseq2d
    @4
    cB
    com
    wcel
    #
    @1
    ssid
    a1i
    @5
    com
    wcel
    #
    @12
    wa
    cB
    @5
    wss
    #
    wa
    @6
    @9
    wss
    #
    @7
    @10
    @13
    @15
    @12
    @14
    vx
    vy
    @5
    cF
    cG
    ackbij.f
    ackbij.g
    ackbij2lem3
    ad2antrr
    @1
    @6
    @9
    sstr2
    syl5com
    findsg
end
