include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cpell14qr.mm"
include "cfv.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "cmul.mm"
include "cc.mm"
include "wa.mm"
include "pell14qrre.mm"
include "recnd.mm"
include "3adant3.mm"
include "3adant2.mm"
include "cc0.mm"
include "wne.mm"
include "pell14qrne0.mm"
include "divrecd.mm"
include "pell14qrreccl.mm"
include "pell14qrmulcl.mm"
include "syld3an3.mm"
include "eqeltrd.mm"

theorem pell14qrdivcl
  let cA: class A
  let cB: class B
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) /\ B e. ( Pell14QR ` D ) ) -> ( A / B ) e. ( Pell14QR ` D ) )

  proof
    cD
    cn
    csquarenn
    cdif
    wcel
    #
    cA
    cD
    cpell14qr
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    w3a
    #
    cA
    cB
    cdiv
    co
    cA
    c1
    cB
    cdiv
    co
    #
    cmul
    co
    #
    @1
    @4
    cA
    cB
    @0
    @2
    cA
    cc
    wcel
    @3
    @0
    @2
    wa
    cA
    cA
    cD
    pell14qrre
    recnd
    3adant3
    @0
    @3
    cB
    cc
    wcel
    @2
    @0
    @3
    wa
    cB
    cB
    cD
    pell14qrre
    recnd
    3adant2
    @0
    @3
    cB
    cc0
    wne
    @2
    cB
    cD
    pell14qrne0
    3adant2
    divrecd
    @0
    @2
    @3
    @5
    @1
    wcel
    #
    @6
    @1
    wcel
    @0
    @3
    @7
    @2
    cB
    cD
    pell14qrreccl
    3adant2
    cA
    @5
    cD
    pell14qrmulcl
    syld3an3
    eqeltrd
end
