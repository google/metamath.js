include "cpsmet.mm"
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
include "blfps.mm"
include "ffn.mm"
include "syl.mm"
include "fnovrn.mm"
include "syl3an1.mm"

theorem blelrnps
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


  assert |- ( ( D e. ( PsMet ` X ) /\ P e. X /\ R e. RR* ) -> ( P ( ball ` D ) R ) e. ran ( ball ` D ) )

  proof
    cD
    cX
    cpsmet
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
    blfps
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
