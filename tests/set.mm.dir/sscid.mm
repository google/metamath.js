include "cxp.mm"
include "wfn.mm"
include "wcel.mm"
include "wa.mm"
include "cres.mm"
include "cssc.mm"
include "wceq.mm"
include "fnresdm.mm"
include "adantr.mm"
include "sscres.mm"
include "eqbrtrrd.mm"

theorem sscid
  let cS: class S
  let cH: class H
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cT: class T


  assert |- ( ( H Fn ( S X. S ) /\ S e. V ) -> H C_cat H )

  proof
    cH
    cS
    cS
    cxp
    #
    wfn
    #
    cS
    cV
    wcel
    #
    wa
    cH
    @0
    cres
    #
    cH
    cH
    cssc
    @1
    @3
    cH
    wceq
    @2
    @0
    cH
    fnresdm
    adantr
    cS
    cS
    cH
    cV
    sscres
    eqbrtrrd
end
