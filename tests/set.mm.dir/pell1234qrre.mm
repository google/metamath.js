include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cpell1234qr.mm"
include "cfv.mm"
include "cr.mm"
include "cv.mm"
include "csqrt.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "c2.mm"
include "cexp.mm"
include "cmin.mm"
include "c1.mm"
include "wa.mm"
include "cz.mm"
include "wrex.mm"
include "elpell1234qr.mm"
include "simprbda.mm"

theorem pell1234qrre
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


  assert |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell1234QR ` D ) ) -> A e. RR )

  proof
    cD
    cn
    csquarenn
    cdif
    wcel
    cA
    cD
    cpell1234qr
    cfv
    wcel
    cA
    cr
    wcel
    cA
    va
    cv
    #
    cD
    csqrt
    cfv
    vb
    cv
    #
    cmul
    co
    caddc
    co
    wceq
    @0
    c2
    cexp
    co
    cD
    @1
    c2
    cexp
    co
    cmul
    co
    cmin
    co
    c1
    wceq
    wa
    vb
    cz
    wrex
    va
    cz
    wrex
    va
    vb
    cA
    cD
    elpell1234qr
    simprbda
end
