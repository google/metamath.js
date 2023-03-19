include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cpell1qr.mm"
include "cfv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
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
include "elpell1qr.mm"
include "1red.mm"
include "simplrl.mm"
include "nn0red.mm"
include "eldifi.mm"
include "ad3antrrr.mm"
include "nnnn0d.mm"
include "nn0ge0d.mm"
include "resqrtcld.mm"
include "simplrr.mm"
include "remulcld.mm"
include "readdcld.mm"
include "cc0.mm"
include "2nn0.mm"
include "a1i.mm"
include "nn0expcld.mm"
include "nn0mulcld.mm"
include "addge02d.mm"
include "mpbid.mm"
include "sq1.mm"
include "cc.mm"
include "nn0cn.mm"
include "ad2antrl.mm"
include "sqcld.mm"
include "ad2antrr.mm"
include "nncnd.mm"
include "ad2antll.mm"
include "mulcld.mm"
include "1cnd.mm"
include "subaddd.mm"
include "biimpa.mm"
include "eqcomd.mm"
include "3brtr4d.mm"
include "0le1.mm"
include "le2sqd.mm"
include "mpbird.mm"
include "sqrtge0d.mm"
include "mulge0d.mm"
include "addge01d.mm"
include "letrd.mm"
include "adantrl.mm"
include "simprl.mm"
include "breqtrrd.mm"
include "ex.mm"
include "rexlimdvva.mm"
include "expimpd.mm"
include "sylbid.mm"
include "imp.mm"

theorem pell1qrge1
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


  assert |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell1QR ` D ) ) -> 1 <_ A )

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
    cle
    wbr
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
    @2
    va
    vb
    cA
    cD
    elpell1qr
    @0
    @3
    @15
    @2
    @0
    @3
    wa
    #
    @14
    @2
    va
    vb
    cn0
    cn0
    @16
    @4
    cn0
    wcel
    #
    @6
    cn0
    wcel
    #
    wa
    #
    wa
    #
    @14
    @2
    @20
    @14
    wa
    c1
    @8
    cA
    cle
    @20
    @13
    c1
    @8
    cle
    wbr
    @9
    @20
    @13
    wa
    #
    c1
    @4
    @8
    @21
    1red
    #
    @21
    @4
    @16
    @17
    @18
    @13
    simplrl
    #
    nn0red
    #
    @21
    @4
    @7
    @24
    @21
    @5
    @6
    @21
    cD
    @21
    cD
    @21
    cD
    @0
    cD
    cn
    wcel
    #
    @3
    @19
    @13
    cD
    cn
    csquarenn
    eldifi
    #
    ad3antrrr
    nnnn0d
    #
    nn0red
    #
    @21
    cD
    @27
    nn0ge0d
    #
    resqrtcld
    #
    @21
    @6
    @16
    @17
    @18
    @13
    simplrr
    #
    nn0red
    #
    remulcld
    #
    readdcld
    @21
    c1
    @4
    cle
    wbr
    c1
    c2
    cexp
    co
    #
    @10
    cle
    wbr
    @21
    c1
    @12
    c1
    caddc
    co
    #
    @34
    @10
    cle
    @21
    cc0
    @12
    cle
    wbr
    c1
    @35
    cle
    wbr
    @21
    @12
    @21
    cD
    @11
    @27
    @21
    @6
    c2
    @31
    c2
    cn0
    wcel
    @21
    2nn0
    a1i
    nn0expcld
    nn0mulcld
    #
    nn0ge0d
    @21
    c1
    @12
    @22
    @21
    @12
    @36
    nn0red
    addge02d
    mpbid
    @34
    c1
    wceq
    @21
    sq1
    a1i
    @21
    @35
    @10
    @20
    @13
    @35
    @10
    wceq
    @20
    @10
    @12
    c1
    @20
    @4
    @17
    @4
    cc
    wcel
    @16
    @18
    @4
    nn0cn
    ad2antrl
    sqcld
    @20
    cD
    @11
    @20
    cD
    @0
    @25
    @3
    @19
    @26
    ad2antrr
    nncnd
    @20
    @6
    @18
    @6
    cc
    wcel
    @16
    @17
    @6
    nn0cn
    ad2antll
    sqcld
    mulcld
    @20
    1cnd
    subaddd
    biimpa
    eqcomd
    3brtr4d
    @21
    c1
    @4
    @22
    @24
    cc0
    c1
    cle
    wbr
    @21
    0le1
    a1i
    @21
    @4
    @23
    nn0ge0d
    le2sqd
    mpbird
    @21
    cc0
    @7
    cle
    wbr
    @4
    @8
    cle
    wbr
    @21
    @5
    @6
    @30
    @32
    @21
    cD
    @28
    @29
    sqrtge0d
    @21
    @6
    @31
    nn0ge0d
    mulge0d
    @21
    @4
    @7
    @24
    @33
    addge01d
    mpbid
    letrd
    adantrl
    @20
    @9
    @13
    simprl
    breqtrrd
    ex
    rexlimdvva
    expimpd
    sylbid
    imp
end
