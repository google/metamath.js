include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "c1.mm"
include "cpell1qr.mm"
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
include "wa.mm"
include "cn0.mm"
include "wrex.mm"
include "1red.mm"
include "cc0.mm"
include "1nn0.mm"
include "a1i.mm"
include "0nn0.mm"
include "eldifi.mm"
include "nncnd.mm"
include "sqrtcld.mm"
include "mul01d.mm"
include "oveq2d.mm"
include "1p0e1.mm"
include "syl6req.mm"
include "sq1.mm"
include "sq0.mm"
include "oveq2i.mm"
include "syl5eq.mm"
include "oveq12d.mm"
include "1m0e1.mm"
include "syl6eq.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "oveq2.mm"
include "rspc2ev.mm"
include "syl112anc.mm"
include "elpell1qr.mm"
include "mpbir2and.mm"

theorem pell1qr1
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


  assert |- ( D e. ( NN \ []NN ) -> 1 e. ( Pell1QR ` D ) )

  proof
    cD
    cn
    csquarenn
    cdif
    wcel
    #
    c1
    cD
    cpell1qr
    cfv
    wcel
    c1
    cr
    wcel
    c1
    va
    cv
    #
    cD
    csqrt
    cfv
    #
    vb
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @1
    c2
    cexp
    co
    #
    cD
    @3
    c2
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    c1
    wceq
    #
    wa
    #
    vb
    cn0
    wrex
    va
    cn0
    wrex
    #
    @0
    1red
    @0
    c1
    cn0
    wcel
    #
    cc0
    cn0
    wcel
    #
    c1
    c1
    @2
    cc0
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    c1
    c2
    cexp
    co
    #
    cD
    cc0
    c2
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    c1
    wceq
    #
    @13
    @14
    @0
    1nn0
    a1i
    @15
    @0
    0nn0
    a1i
    @0
    @17
    c1
    cc0
    caddc
    co
    c1
    @0
    @16
    cc0
    c1
    caddc
    @0
    @2
    @0
    cD
    @0
    cD
    cD
    cn
    csquarenn
    eldifi
    nncnd
    #
    sqrtcld
    mul01d
    oveq2d
    1p0e1
    syl6req
    @0
    @22
    c1
    cc0
    cmin
    co
    c1
    @0
    @19
    c1
    @21
    cc0
    cmin
    @19
    c1
    wceq
    @0
    sq1
    a1i
    @0
    @21
    cD
    cc0
    cmul
    co
    cc0
    @20
    cc0
    cD
    cmul
    sq0
    oveq2i
    @0
    cD
    @24
    mul01d
    syl5eq
    oveq12d
    1m0e1
    syl6eq
    @12
    @18
    @23
    wa
    c1
    c1
    @4
    caddc
    co
    #
    wceq
    #
    @19
    @9
    cmin
    co
    #
    c1
    wceq
    #
    wa
    va
    vb
    c1
    cc0
    cn0
    cn0
    @1
    c1
    wceq
    #
    @6
    @26
    @11
    @28
    @29
    @5
    @25
    c1
    @1
    c1
    @4
    caddc
    oveq1
    eqeq2d
    @29
    @10
    @27
    c1
    @29
    @7
    @19
    @9
    cmin
    @1
    c1
    c2
    cexp
    oveq1
    oveq1d
    eqeq1d
    anbi12d
    @3
    cc0
    wceq
    #
    @26
    @18
    @28
    @23
    @30
    @25
    @17
    c1
    @30
    @4
    @16
    c1
    caddc
    @3
    cc0
    @2
    cmul
    oveq2
    oveq2d
    eqeq2d
    @30
    @27
    @22
    c1
    @30
    @9
    @21
    @19
    cmin
    @30
    @8
    @20
    cD
    cmul
    @3
    cc0
    c2
    cexp
    oveq1
    oveq2d
    oveq2d
    eqeq1d
    anbi12d
    rspc2ev
    syl112anc
    va
    vb
    c1
    cD
    elpell1qr
    mpbir2and
end
