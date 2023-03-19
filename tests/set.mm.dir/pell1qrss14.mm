include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cpell1qr.mm"
include "cfv.mm"
include "cpell14qr.mm"
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
include "cn0.mm"
include "wrex.mm"
include "cz.mm"
include "wi.mm"
include "nn0z.mm"
include "a1i.mm"
include "anim1d.mm"
include "reximdv2.mm"
include "reximdv.mm"
include "anim2d.mm"
include "elpell1qr.mm"
include "elpell14qr.mm"
include "3imtr4d.mm"
include "ssrdv.mm"

theorem pell1qrss14
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


  assert |- ( D e. ( NN \ []NN ) -> ( Pell1QR ` D ) C_ ( Pell14QR ` D ) )

  proof
    cD
    cn
    csquarenn
    cdif
    wcel
    #
    va
    cD
    cpell1qr
    cfv
    #
    cD
    cpell14qr
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
    vc
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
    #
    vb
    cn0
    wrex
    #
    vc
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
    vc
    cn0
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
    @9
    @11
    @4
    @0
    @8
    @10
    vc
    cn0
    @0
    @7
    @7
    vb
    cn0
    cz
    @0
    @6
    cn0
    wcel
    #
    @6
    cz
    wcel
    #
    @7
    @12
    @13
    wi
    @0
    @6
    nn0z
    a1i
    anim1d
    reximdv2
    reximdv
    anim2d
    vc
    vb
    @3
    cD
    elpell1qr
    vc
    vb
    @3
    cD
    elpell14qr
    3imtr4d
    ssrdv
end
