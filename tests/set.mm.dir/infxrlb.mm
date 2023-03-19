include "cxr.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "cinf.mm"
include "infxrcl.mm"
include "adantr.mm"
include "ssel2.mm"
include "wbr.mm"
include "wn.mm"
include "wor.mm"
include "xrltso.mm"
include "a1i.mm"
include "xrinfmss.mm"
include "inflb.mm"
include "imp.mm"
include "xrnltled.mm"

theorem infxrlb
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A C_ RR* /\ B e. A ) -> inf ( A , RR* , < ) <_ B )

  proof
    cA
    cxr
    wss
    #
    cB
    cA
    wcel
    #
    wa
    cA
    cxr
    clt
    cinf
    #
    cB
    @0
    @2
    cxr
    wcel
    @1
    cA
    infxrcl
    adantr
    cA
    cxr
    cB
    ssel2
    @0
    @1
    cB
    @2
    clt
    wbr
    wn
    @0
    vx
    vy
    vz
    cxr
    cA
    cB
    clt
    cxr
    clt
    wor
    @0
    xrltso
    a1i
    vx
    vy
    vz
    cA
    xrinfmss
    inflb
    imp
    xrnltled
end
