include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cxr.mm"
include "w3a.mm"
include "cbl.mm"
include "co.mm"
include "cxp.mm"
include "cpw.mm"
include "wf.mm"
include "blf.mm"
include "fovrn.mm"
include "syl3an1.mm"
include "elpwid.mm"

theorem blssm
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


  assert |- ( ( D e. ( *Met ` X ) /\ P e. X /\ R e. RR* ) -> ( P ( ball ` D ) R ) C_ X )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cP
    cX
    wcel
    #
    cR
    cxr
    wcel
    #
    w3a
    cP
    cR
    cD
    cbl
    cfv
    #
    co
    #
    cX
    @0
    cX
    cxr
    cxp
    cX
    cpw
    #
    @3
    wf
    @1
    @2
    @4
    @5
    wcel
    cD
    cX
    blf
    cP
    cR
    @5
    cX
    cxr
    @3
    fovrn
    syl3an1
    elpwid
end
