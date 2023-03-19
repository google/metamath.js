include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cfn.mm"
include "wcel.mm"
include "w3a.mm"
include "ctop.mm"
include "cint.mm"
include "wi.mm"
include "cpw.mm"
include "elpwg.mm"
include "cv.mm"
include "wceq.mm"
include "sseq1.mm"
include "neeq1.mm"
include "eleq1.mm"
include "3anbi123d.mm"
include "inteq.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "imbi12d.mm"
include "cuni.mm"
include "wal.mm"
include "wa.mm"
include "sp.mm"
include "adantl.mm"
include "istop2g.mm"
include "ibi.mm"
include "syl11.mm"
include "vtoclg.mm"
include "com12.mm"
include "3exp.mm"
include "com3r.mm"
include "com4r.mm"
include "syl6bir.mm"
include "pm2.43a.mm"
include "com4l.mm"
include "pm2.43i.mm"
include "3imp.mm"

theorem fiinopn
  let cA: class A
  let cJ: class J
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( J e. Top -> ( ( A C_ J /\ A =/= (/) /\ A e. Fin ) -> |^| A e. J ) )

  proof
    cA
    cJ
    wss
    #
    cA
    c0
    wne
    #
    cA
    cfn
    wcel
    #
    w3a
    #
    cJ
    ctop
    wcel
    #
    cA
    cint
    #
    cJ
    wcel
    #
    @0
    @1
    @2
    @4
    @6
    wi
    #
    @0
    @1
    @2
    @7
    wi
    wi
    @2
    @0
    @0
    @1
    @7
    @0
    @2
    @0
    @1
    @7
    wi
    wi
    #
    @2
    @0
    cA
    cJ
    cpw
    #
    wcel
    #
    @2
    @8
    wi
    cA
    cJ
    cfn
    elpwg
    @2
    @0
    @1
    @10
    @7
    @0
    @1
    @2
    @10
    @7
    wi
    #
    @0
    @1
    @2
    @11
    @10
    @3
    @7
    vx
    cv
    #
    cJ
    wss
    #
    @12
    c0
    wne
    #
    @12
    cfn
    wcel
    #
    w3a
    #
    @4
    @12
    cint
    #
    cJ
    wcel
    #
    wi
    #
    wi
    @3
    @7
    wi
    vx
    cA
    @9
    @12
    cA
    wceq
    #
    @16
    @3
    @19
    @7
    @20
    @13
    @0
    @14
    @1
    @15
    @2
    @12
    cA
    cJ
    sseq1
    @12
    cA
    c0
    neeq1
    @12
    cA
    cfn
    eleq1
    3anbi123d
    @20
    @18
    @6
    @4
    @20
    @17
    @5
    cJ
    @12
    cA
    inteq
    eleq1d
    imbi2d
    imbi12d
    @13
    @12
    cuni
    cJ
    wcel
    wi
    vx
    wal
    #
    @16
    @18
    wi
    #
    vx
    wal
    #
    wa
    #
    @16
    @18
    @4
    @23
    @22
    @21
    @22
    vx
    sp
    adantl
    @4
    @24
    vx
    ctop
    cJ
    istop2g
    ibi
    syl11
    vtoclg
    com12
    3exp
    com3r
    com4r
    syl6bir
    pm2.43a
    com4l
    pm2.43i
    3imp
    com12
end
