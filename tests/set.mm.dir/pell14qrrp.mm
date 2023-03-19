include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cpell14qr.mm"
include "cfv.mm"
include "wa.mm"
include "pell14qrre.mm"
include "pell14qrgt0.mm"
include "elrpd.mm"

theorem pell14qrrp
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


  assert |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) ) -> A e. RR+ )

  proof
    cD
    cn
    csquarenn
    cdif
    wcel
    cA
    cD
    cpell14qr
    cfv
    wcel
    wa
    cA
    cA
    cD
    pell14qrre
    cA
    cD
    pell14qrgt0
    elrpd
end
