include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cxr.mm"
include "w3a.mm"
include "cbl.mm"
include "co.mm"
include "wa.mm"
include "cc0.mm"
include "0xr.mm"
include "a1i.mm"
include "simpl1.mm"
include "simpl2.mm"
include "clt.mm"
include "wbr.mm"
include "elbl.mm"
include "simprbda.mm"
include "xmetcl.mm"
include "syl3anc.mm"
include "simpl3.mm"
include "cle.mm"
include "xmetge0.mm"
include "simplbda.mm"
include "xrlelttrd.mm"

theorem blgt0
  let cA: class A
  let cD: class D
  let cP: class P
  let cR: class R
  let cX: class X
  let vx: setvar x
  let vr: setvar r
  let vy: setvar y
  let wph: wff ph
  let cQ: class Q
  let cS: class S


  assert |- ( ( ( D e. ( *Met ` X ) /\ P e. X /\ R e. RR* ) /\ A e. ( P ( ball ` D ) R ) ) -> 0 < R )

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
    #
    cA
    cP
    cR
    cD
    cbl
    cfv
    co
    wcel
    #
    wa
    #
    cc0
    cP
    cA
    cD
    co
    #
    cR
    cc0
    cxr
    wcel
    @5
    0xr
    a1i
    @5
    @0
    @1
    cA
    cX
    wcel
    #
    @6
    cxr
    wcel
    @0
    @1
    @2
    @4
    simpl1
    #
    @0
    @1
    @2
    @4
    simpl2
    #
    @3
    @4
    @7
    @6
    cR
    clt
    wbr
    #
    cA
    cD
    cP
    cR
    cX
    elbl
    #
    simprbda
    #
    cP
    cA
    cD
    cX
    xmetcl
    syl3anc
    @0
    @1
    @2
    @4
    simpl3
    @5
    @0
    @1
    @7
    cc0
    @6
    cle
    wbr
    @8
    @9
    @12
    cP
    cA
    cD
    cX
    xmetge0
    syl3anc
    @3
    @4
    @7
    @10
    @11
    simplbda
    xrlelttrd
end
