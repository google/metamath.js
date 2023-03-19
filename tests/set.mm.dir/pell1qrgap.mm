include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cpell1qr.mm"
include "cfv.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "csqrt.mm"
include "cle.mm"
include "wi.mm"
include "wa.mm"
include "cr.mm"
include "cv.mm"
include "cmul.mm"
include "wceq.mm"
include "c2.mm"
include "cexp.mm"
include "cmin.mm"
include "cn0.mm"
include "wrex.mm"
include "wb.mm"
include "elpell1qr.mm"
include "adantr.mm"
include "eldifi.mm"
include "ad4antr.mm"
include "simplr.mm"
include "simp-4r.mm"
include "simprl.mm"
include "breqtrd.mm"
include "simprr.mm"
include "pell1qrgaplem.mm"
include "syl22anc.mm"
include "breqtrrd.mm"
include "ex.mm"
include "rexlimdvva.mm"
include "expimpd.mm"
include "sylbid.mm"
include "com23.mm"
include "3imp.mm"

theorem pell1qrgap
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


  assert |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell1QR ` D ) /\ 1 < A ) -> ( ( sqrt ` ( D + 1 ) ) + ( sqrt ` D ) ) <_ A )

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
    #
    caddc
    co
    #
    cA
    cle
    wbr
    #
    @0
    @2
    @1
    @5
    @0
    @2
    @1
    @5
    wi
    @0
    @2
    wa
    #
    @1
    cA
    cr
    wcel
    #
    cA
    va
    cv
    #
    @3
    vb
    cv
    #
    cmul
    co
    caddc
    co
    #
    wceq
    #
    @8
    c2
    cexp
    co
    cD
    @9
    c2
    cexp
    co
    cmul
    co
    cmin
    co
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
    wa
    #
    @5
    @0
    @1
    @15
    wb
    @2
    va
    vb
    cA
    cD
    elpell1qr
    adantr
    @6
    @7
    @14
    @5
    @6
    @7
    wa
    #
    @13
    @5
    va
    vb
    cn0
    cn0
    @16
    @8
    cn0
    wcel
    @9
    cn0
    wcel
    wa
    #
    wa
    #
    @13
    @5
    @18
    @13
    wa
    #
    @4
    @10
    cA
    cle
    @19
    cD
    cn
    wcel
    #
    @17
    c1
    @10
    clt
    wbr
    @12
    @4
    @10
    cle
    wbr
    @0
    @20
    @2
    @7
    @17
    @13
    cD
    cn
    csquarenn
    eldifi
    ad4antr
    @16
    @17
    @13
    simplr
    @19
    c1
    cA
    @10
    clt
    @0
    @2
    @7
    @17
    @13
    simp-4r
    @18
    @11
    @12
    simprl
    #
    breqtrd
    @18
    @11
    @12
    simprr
    @8
    @9
    cD
    pell1qrgaplem
    syl22anc
    @21
    breqtrrd
    ex
    rexlimdvva
    expimpd
    sylbid
    ex
    com23
    3imp
end
