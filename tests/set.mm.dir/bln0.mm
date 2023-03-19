include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "crp.mm"
include "w3a.mm"
include "cbl.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "blcntr.mm"
include "ne0i.mm"
include "syl.mm"

theorem bln0
  let cD: class D
  let cP: class P
  let cR: class R
  let cX: class X
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cS: class S


  assert |- ( ( D e. ( *Met ` X ) /\ P e. X /\ R e. RR+ ) -> ( P ( ball ` D ) R ) =/= (/) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    cP
    cX
    wcel
    cR
    crp
    wcel
    w3a
    cP
    cP
    cR
    cD
    cbl
    cfv
    co
    #
    wcel
    @0
    c0
    wne
    cD
    cP
    cR
    cX
    blcntr
    @0
    cP
    ne0i
    syl
end
