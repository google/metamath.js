include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cpell14qr.mm"
include "cfv.mm"
include "cpell1234qr.mm"
include "cr.mm"
include "pell14qrss1234.mm"
include "sselda.mm"
include "pell1234qrre.mm"
include "syldan.mm"

theorem pell14qrre
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


  assert |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) ) -> A e. RR )

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
    cA
    cD
    cpell1234qr
    cfv
    #
    wcel
    cA
    cr
    wcel
    @0
    @1
    @2
    cA
    cD
    pell14qrss1234
    sselda
    cA
    cD
    pell1234qrre
    syldan
end
