include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cpell1qr.mm"
include "cfv.mm"
include "cpell14qr.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "csqrt.mm"
include "cle.mm"
include "w3a.mm"
include "simp2.mm"
include "wa.mm"
include "cr.mm"
include "wi.mm"
include "1re.mm"
include "pell14qrre.mm"
include "ltle.mm"
include "sylancr.mm"
include "3impia.mm"
include "wb.mm"
include "elpell1qr2.mm"
include "3ad2ant1.mm"
include "mpbir2and.mm"
include "pell1qrgap.mm"
include "syld3an2.mm"

theorem pell14qrgap
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


  assert |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) /\ 1 < A ) -> ( ( sqrt ` ( D + 1 ) ) + ( sqrt ` D ) ) <_ A )

  proof
    cD
    cn
    csquarenn
    cdif
    wcel
    #
    cA
    cD
    cpell1qr
    cfv
    wcel
    #
    cA
    cD
    cpell14qr
    cfv
    wcel
    #
    c1
    cA
    clt
    wbr
    #
    cD
    c1
    caddc
    co
    csqrt
    cfv
    cD
    csqrt
    cfv
    caddc
    co
    cA
    cle
    wbr
    @0
    @2
    @3
    w3a
    @1
    @2
    c1
    cA
    cle
    wbr
    #
    @0
    @2
    @3
    simp2
    @0
    @2
    @3
    @4
    @0
    @2
    wa
    c1
    cr
    wcel
    cA
    cr
    wcel
    @3
    @4
    wi
    1re
    cA
    cD
    pell14qrre
    c1
    cA
    ltle
    sylancr
    3impia
    @0
    @2
    @1
    @2
    @4
    wa
    wb
    @3
    cA
    cD
    elpell1qr2
    3ad2ant1
    mpbir2and
    cA
    cD
    pell1qrgap
    syld3an2
end
