include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cpell14qr.mm"
include "cfv.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cpell1234qr.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "pell1234qrreccl.mm"
include "adantrr.mm"
include "cr.mm"
include "pell1234qrre.mm"
include "simprr.mm"
include "recgt0d.mm"
include "jca.mm"
include "ex.mm"
include "elpell14qr2.mm"
include "3imtr4d.mm"
include "imp.mm"

theorem pell14qrreccl
  let cA: class A
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) ) -> ( 1 / A ) e. ( Pell14QR ` D ) )

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
    c1
    cA
    cdiv
    co
    #
    @1
    wcel
    #
    @0
    cA
    cD
    cpell1234qr
    cfv
    #
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    wa
    #
    @3
    @5
    wcel
    #
    cc0
    @3
    clt
    wbr
    #
    wa
    #
    @2
    @4
    @0
    @8
    @11
    @0
    @8
    wa
    #
    @9
    @10
    @0
    @6
    @9
    @7
    cA
    cD
    pell1234qrreccl
    adantrr
    @12
    cA
    @0
    @6
    cA
    cr
    wcel
    @7
    cA
    cD
    pell1234qrre
    adantrr
    @0
    @6
    @7
    simprr
    recgt0d
    jca
    ex
    cA
    cD
    elpell14qr2
    @3
    cD
    elpell14qr2
    3imtr4d
    imp
end
