include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "wss.mm"
include "wa.mm"
include "simpr.mm"
include "pweq.mm"
include "adantr.mm"
include "rabeqdv.mm"
include "sseq12d.mm"
include "brabga.mm"

theorem isausgr
  let vx: setvar x
  let vv: setvar v
  let ve: setvar e
  let cE: class E
  let cG: class G
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume ausgr.1: |- G = { <. v , e >. | e C_ { x e. ~P v | ( # ` x ) = 2 } }

  disjoint e v
  disjoint e x
  disjoint E e
  disjoint v x
  disjoint E v
  disjoint E x
  disjoint V e
  disjoint V v
  disjoint V x
  disjoint X x
  disjoint Y x
  assert |- ( ( V e. W /\ E e. X ) -> ( V G E <-> E C_ { x e. ~P V | ( # ` x ) = 2 } ) )

  proof
    ve
    cv
    #
    vx
    cv
    chash
    cfv
    c2
    wceq
    #
    vx
    vv
    cv
    #
    cpw
    #
    crab
    #
    wss
    cE
    @1
    vx
    cV
    cpw
    #
    crab
    #
    wss
    vv
    ve
    cV
    cE
    cG
    cW
    cX
    @2
    cV
    wceq
    #
    @0
    cE
    wceq
    #
    wa
    #
    @0
    cE
    @4
    @6
    @7
    @8
    simpr
    @9
    @1
    vx
    @3
    @5
    @7
    @3
    @5
    wceq
    @8
    @2
    cV
    pweq
    adantr
    rabeqdv
    sseq12d
    ausgr.1
    brabga
end
