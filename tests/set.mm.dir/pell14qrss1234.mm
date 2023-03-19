include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cpell14qr.mm"
include "cfv.mm"
include "cpell1234qr.mm"
include "cv.mm"
include "cr.mm"
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
include "cn0.mm"
include "wi.mm"
include "nn0z.mm"
include "a1i.mm"
include "anim1d.mm"
include "reximdv2.mm"
include "anim2d.mm"
include "elpell14qr.mm"
include "elpell1234qr.mm"
include "3imtr4d.mm"
include "ssrdv.mm"

theorem pell14qrss1234
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( D e. ( NN \ []NN ) -> ( Pell14QR ` D ) C_ ( Pell1234QR ` D ) )

  proof
    cD
    cn
    csquarenn
    cdif
    wcel
    #
    va
    cD
    cpell14qr
    cfv
    #
    cD
    cpell1234qr
    cfv
    #
    @0
    va
    cv
    #
    cr
    wcel
    #
    @3
    vb
    cv
    #
    cD
    csqrt
    cfv
    vc
    cv
    #
    cmul
    co
    caddc
    co
    wceq
    @5
    c2
    cexp
    co
    cD
    @6
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
    vc
    cz
    wrex
    #
    vb
    cn0
    wrex
    #
    wa
    @4
    @7
    vb
    cz
    wrex
    #
    wa
    @3
    @1
    wcel
    @3
    @2
    wcel
    @0
    @8
    @9
    @4
    @0
    @7
    @7
    vb
    cn0
    cz
    @0
    @5
    cn0
    wcel
    #
    @5
    cz
    wcel
    #
    @7
    @10
    @11
    wi
    @0
    @5
    nn0z
    a1i
    anim1d
    reximdv2
    anim2d
    vb
    vc
    @3
    cD
    elpell14qr
    vb
    vc
    @3
    cD
    elpell1234qr
    3imtr4d
    ssrdv
end
