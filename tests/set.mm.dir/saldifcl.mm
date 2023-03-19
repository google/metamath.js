include "csalg.mm"
include "wcel.mm"
include "wa.mm"
include "cuni.mm"
include "cv.mm"
include "cdif.mm"
include "wceq.mm"
include "difeq2.mm"
include "eleq1d.mm"
include "wral.mm"
include "c0.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wi.mm"
include "cpw.mm"
include "w3a.mm"
include "issal.mm"
include "ibi.mm"
include "simp2d.mm"
include "adantr.mm"
include "simpr.mm"
include "rspcdva.mm"

theorem saldifcl
  let cS: class S
  let cE: class E
  let vy: setvar y
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( S e. SAlg /\ E e. S ) -> ( U. S \ E ) e. S )

  proof
    cS
    csalg
    wcel
    #
    cE
    cS
    wcel
    #
    wa
    cS
    cuni
    #
    vy
    cv
    #
    cdif
    #
    cS
    wcel
    #
    @2
    cE
    cdif
    #
    cS
    wcel
    vy
    cS
    cE
    @3
    cE
    wceq
    @4
    @6
    cS
    @3
    cE
    @2
    difeq2
    eleq1d
    @0
    @5
    vy
    cS
    wral
    #
    @1
    @0
    c0
    cS
    wcel
    #
    @7
    @3
    com
    cdom
    wbr
    @3
    cuni
    cS
    wcel
    wi
    vy
    cS
    cpw
    wral
    #
    @0
    @8
    @7
    @9
    w3a
    vy
    cS
    csalg
    issal
    ibi
    simp2d
    adantr
    @0
    @1
    simpr
    rspcdva
end
