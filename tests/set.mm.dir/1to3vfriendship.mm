include "wcel.mm"
include "csn.mm"
include "wceq.mm"
include "cpr.mm"
include "ctp.mm"
include "w3o.mm"
include "wa.mm"
include "cfrgr.mm"
include "cv.mm"
include "cdif.mm"
include "wreu.mm"
include "wral.mm"
include "wrex.mm"
include "1to3vfriswmgr.mm"
include "prcom.mm"
include "eleq1i.mm"
include "biimpi.mm"
include "adantr.mm"
include "ralimi.mm"
include "reximi.mm"
include "syl6.mm"

theorem 1to3vfriendship
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let vy: setvar y
  let cY: class Y
  let vh: setvar h
  let vx: setvar x
  assume 3vfriswmgr.v: |- V = ( Vtx ` G )
  assume 3vfriswmgr.e: |- E = ( Edg ` G )

  disjoint A w
  disjoint B w
  disjoint C w
  disjoint E w
  disjoint G w
  disjoint V w
  disjoint X w
  disjoint A v
  disjoint v w
  disjoint B v
  disjoint C v
  disjoint E v
  disjoint V v
  disjoint A y
  disjoint w y
  disjoint B y
  disjoint C y
  disjoint E y
  disjoint G y
  disjoint V y
  disjoint X y
  disjoint Y w
  disjoint Y y
  disjoint A h
  disjoint h v
  disjoint h w
  disjoint B h
  disjoint C h
  disjoint E h
  disjoint V h
  disjoint A x
  disjoint v x
  disjoint w x
  disjoint B x
  disjoint C x
  disjoint E x
  disjoint G x
  disjoint V x
  disjoint X x
  assert |- ( ( A e. X /\ ( V = { A } \/ V = { A , B } \/ V = { A , B , C } ) ) -> ( G e. FriendGraph -> E. v e. V A. w e. ( V \ { v } ) { v , w } e. E ) )

  proof
    cA
    cX
    wcel
    cV
    cA
    csn
    wceq
    cV
    cA
    cB
    cpr
    wceq
    cV
    cA
    cB
    cC
    ctp
    wceq
    w3o
    wa
    cG
    cfrgr
    wcel
    vw
    cv
    #
    vv
    cv
    #
    cpr
    #
    cE
    wcel
    #
    @0
    vx
    cv
    cpr
    cE
    wcel
    vx
    cV
    @1
    csn
    cdif
    #
    wreu
    #
    wa
    #
    vw
    @4
    wral
    #
    vv
    cV
    wrex
    @1
    @0
    cpr
    #
    cE
    wcel
    #
    vw
    @4
    wral
    #
    vv
    cV
    wrex
    vx
    vw
    cA
    cB
    cC
    vv
    cE
    cG
    cV
    cX
    3vfriswmgr.v
    3vfriswmgr.e
    1to3vfriswmgr
    @7
    @10
    vv
    cV
    @6
    @9
    vw
    @4
    @3
    @9
    @5
    @3
    @9
    @2
    @8
    cE
    @0
    @1
    prcom
    eleq1i
    biimpi
    adantr
    ralimi
    reximi
    syl6
end
