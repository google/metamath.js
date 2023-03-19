include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cbl.mm"
include "cxr.mm"
include "cxp.mm"
include "wfn.mm"
include "co.mm"
include "crn.mm"
include "cpw.mm"
include "wf.mm"
include "blf.mm"
include "ffn.mm"
include "syl.mm"
include "fnovrn.mm"
include "syl3an1.mm"

theorem blelrn
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


  assert |- ( ( D e. ( *Met ` X ) /\ P e. X /\ R e. RR* ) -> ( P ( ball ` D ) R ) e. ran ( ball ` D ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cD
    cbl
    cfv
    #
    cX
    cxr
    cxp
    #
    wfn
    #
    cP
    cX
    wcel
    cR
    cxr
    wcel
    cP
    cR
    @1
    co
    @1
    crn
    wcel
    @0
    @2
    cX
    cpw
    #
    @1
    wf
    @3
    cD
    cX
    blf
    @2
    @4
    @1
    ffn
    syl
    cX
    cxr
    cP
    cR
    @1
    fnovrn
    syl3an1
end
