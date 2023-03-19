include "wcel.mm"
include "wfr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wal.mm"
include "df-fr.mm"
include "wceq.mm"
include "sseq1.mm"
include "neeq1.mm"
include "anbi12d.mm"
include "raleq.mm"
include "rexeqbi1dv.mm"
include "imbi12d.mm"
include "spcgv.mm"
include "syl5bi.mm"
include "imp31.mm"

theorem fri
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vz: setvar z
  let cV: class V

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint R x
  disjoint R y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint R z
  disjoint V x
  disjoint V y
  assert |- ( ( ( B e. C /\ R Fr A ) /\ ( B C_ A /\ B =/= (/) ) ) -> E. x e. B A. y e. B -. y R x )

  proof
    cB
    cC
    wcel
    #
    cA
    cR
    wfr
    #
    cB
    cA
    wss
    #
    cB
    c0
    wne
    #
    wa
    #
    vy
    cv
    vx
    cv
    cR
    wbr
    wn
    #
    vy
    cB
    wral
    #
    vx
    cB
    wrex
    #
    @1
    vz
    cv
    #
    cA
    wss
    #
    @8
    c0
    wne
    #
    wa
    #
    @5
    vy
    @8
    wral
    #
    vx
    @8
    wrex
    #
    wi
    #
    vz
    wal
    @0
    @4
    @7
    wi
    #
    vz
    vx
    vy
    cA
    cR
    df-fr
    @14
    @15
    vz
    cB
    cC
    @8
    cB
    wceq
    #
    @11
    @4
    @13
    @7
    @16
    @9
    @2
    @10
    @3
    @8
    cB
    cA
    sseq1
    @8
    cB
    c0
    neeq1
    anbi12d
    @12
    @6
    vx
    @8
    cB
    @5
    vy
    @8
    cB
    raleq
    rexeqbi1dv
    imbi12d
    spcgv
    syl5bi
    imp31
end
