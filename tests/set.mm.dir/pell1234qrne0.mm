include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cpell1234qr.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
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
include "simprl.mm"
include "ax-1ne0.mm"
include "cc.mm"
include "eldifi.mm"
include "adantr.mm"
include "nncnd.mm"
include "ad3antrrr.mm"
include "sqrtcld.mm"
include "zcn.mm"
include "ad2antll.mm"
include "ad2antrr.mm"
include "sqmuld.mm"
include "sqsqrtd.mm"
include "oveq1d.mm"
include "eqtr2d.mm"
include "oveq2d.mm"
include "ad2antrl.mm"
include "mulcld.mm"
include "subsq.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "simplr.mm"
include "simpr.mm"
include "subcld.mm"
include "mul02d.mm"
include "3eqtr3d.mm"
include "ex.mm"
include "necon3d.mm"
include "mpi.mm"
include "adantrl.mm"
include "eqnetrd.mm"
include "rexlimdvva.mm"
include "expimpd.mm"
include "sylbid.mm"
include "imp.mm"

theorem pell1234qrne0
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


  assert |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell1234QR ` D ) ) -> A =/= 0 )

  proof
    cD
    cn
    csquarenn
    cdif
    wcel
    #
    cA
    cD
    cpell1234qr
    cfv
    wcel
    #
    cA
    cc0
    wne
    #
    @0
    @1
    cA
    cr
    wcel
    #
    cA
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
    @4
    c2
    cexp
    co
    #
    cD
    @6
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
    cz
    wrex
    va
    cz
    wrex
    #
    wa
    @2
    va
    vb
    cA
    cD
    elpell1234qr
    @0
    @3
    @16
    @2
    @0
    @3
    wa
    #
    @15
    @2
    va
    vb
    cz
    cz
    @17
    @4
    cz
    wcel
    #
    @6
    cz
    wcel
    #
    wa
    #
    wa
    #
    @15
    @2
    @21
    @15
    wa
    cA
    @8
    cc0
    @21
    @9
    @14
    simprl
    @21
    @14
    @8
    cc0
    wne
    #
    @9
    @21
    @14
    wa
    #
    c1
    cc0
    wne
    @22
    ax-1ne0
    @23
    @8
    cc0
    c1
    cc0
    @23
    @8
    cc0
    wceq
    #
    c1
    cc0
    wceq
    @23
    @24
    wa
    #
    @13
    @8
    @4
    @7
    cmin
    co
    #
    cmul
    co
    #
    c1
    cc0
    @25
    @13
    @10
    @7
    c2
    cexp
    co
    #
    cmin
    co
    #
    @27
    @25
    @12
    @28
    @10
    cmin
    @25
    @28
    @5
    c2
    cexp
    co
    #
    @11
    cmul
    co
    @12
    @25
    @5
    @6
    @25
    cD
    @17
    cD
    cc
    wcel
    @20
    @14
    @24
    @17
    cD
    @0
    cD
    cn
    wcel
    @3
    cD
    cn
    csquarenn
    eldifi
    adantr
    nncnd
    ad3antrrr
    #
    sqrtcld
    #
    @21
    @6
    cc
    wcel
    #
    @14
    @24
    @19
    @33
    @17
    @18
    @6
    zcn
    ad2antll
    ad2antrr
    #
    sqmuld
    @25
    @30
    cD
    @11
    cmul
    @25
    cD
    @31
    sqsqrtd
    oveq1d
    eqtr2d
    oveq2d
    @25
    @4
    cc
    wcel
    #
    @7
    cc
    wcel
    @29
    @27
    wceq
    @21
    @35
    @14
    @24
    @18
    @35
    @17
    @19
    @4
    zcn
    ad2antrl
    ad2antrr
    #
    @25
    @5
    @6
    @32
    @34
    mulcld
    #
    @4
    @7
    subsq
    syl2anc
    eqtrd
    @21
    @14
    @24
    simplr
    @25
    @27
    cc0
    @26
    cmul
    co
    cc0
    @25
    @8
    cc0
    @26
    cmul
    @23
    @24
    simpr
    oveq1d
    @25
    @26
    @25
    @4
    @7
    @36
    @37
    subcld
    mul02d
    eqtrd
    3eqtr3d
    ex
    necon3d
    mpi
    adantrl
    eqnetrd
    ex
    rexlimdvva
    expimpd
    sylbid
    imp
end
