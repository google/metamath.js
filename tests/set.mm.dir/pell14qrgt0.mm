include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cpell14qr.mm"
include "cfv.mm"
include "cc0.mm"
include "clt.mm"
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
include "c1.mm"
include "wa.mm"
include "cz.mm"
include "wrex.mm"
include "cn0.mm"
include "elpell14qr.mm"
include "cabs.mm"
include "0cnd.mm"
include "eldifi.mm"
include "ad3antrrr.mm"
include "nnred.mm"
include "nnnn0d.mm"
include "nn0ge0d.mm"
include "resqrtcld.mm"
include "zre.mm"
include "adantl.mm"
include "ad2antlr.mm"
include "remulcld.mm"
include "recnd.mm"
include "abssubd.mm"
include "subid1d.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "absresq.mm"
include "syl.mm"
include "sqrtcld.mm"
include "cc.mm"
include "sqmuld.mm"
include "sqsqrtd.mm"
include "oveq1d.mm"
include "3eqtrd.mm"
include "0lt1.mm"
include "simpr.mm"
include "syl5breqr.mm"
include "resqcld.mm"
include "nn0re.mm"
include "adantr.mm"
include "posdifd.mm"
include "mpbird.mm"
include "eqbrtrd.mm"
include "abscld.mm"
include "absge0d.mm"
include "cle.mm"
include "nn0ge0.mm"
include "lt2sqd.mm"
include "0red.mm"
include "absdifltd.mm"
include "mpbid.mm"
include "simprd.mm"
include "nn0cn.mm"
include "addcomd.mm"
include "breqtrrd.mm"
include "adantrl.mm"
include "simprl.mm"
include "ex.mm"
include "rexlimdvva.mm"
include "expimpd.mm"
include "sylbid.mm"
include "imp.mm"

theorem pell14qrgt0
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


  assert |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) ) -> 0 < A )

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
    wcel
    #
    cc0
    cA
    clt
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
    cn0
    wrex
    #
    wa
    @2
    va
    vb
    cA
    cD
    elpell14qr
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
    cn0
    cz
    @17
    @4
    cn0
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
    cc0
    @8
    cA
    clt
    @21
    @14
    cc0
    @8
    clt
    wbr
    @9
    @21
    @14
    wa
    #
    cc0
    @7
    @4
    caddc
    co
    #
    @8
    clt
    @22
    @7
    @4
    cmin
    co
    cc0
    clt
    wbr
    #
    cc0
    @23
    clt
    wbr
    #
    @22
    cc0
    @7
    cmin
    co
    cabs
    cfv
    #
    @4
    clt
    wbr
    @24
    @25
    wa
    @22
    @26
    @7
    cabs
    cfv
    #
    @4
    clt
    @22
    @26
    @7
    cc0
    cmin
    co
    #
    cabs
    cfv
    @27
    @22
    cc0
    @7
    @22
    0cnd
    @22
    @7
    @22
    @5
    @6
    @22
    cD
    @22
    cD
    @0
    cD
    cn
    wcel
    @3
    @20
    @14
    cD
    cn
    csquarenn
    eldifi
    ad3antrrr
    #
    nnred
    #
    @22
    cD
    @22
    cD
    @29
    nnnn0d
    nn0ge0d
    resqrtcld
    @20
    @6
    cr
    wcel
    #
    @17
    @14
    @19
    @31
    @18
    @6
    zre
    adantl
    #
    ad2antlr
    #
    remulcld
    #
    recnd
    #
    abssubd
    @22
    @28
    @7
    cabs
    @22
    @7
    @35
    subid1d
    fveq2d
    eqtrd
    @22
    @27
    @4
    clt
    wbr
    @27
    c2
    cexp
    co
    #
    @10
    clt
    wbr
    @22
    @36
    @12
    @10
    clt
    @22
    @36
    @7
    c2
    cexp
    co
    #
    @5
    c2
    cexp
    co
    #
    @11
    cmul
    co
    @12
    @22
    @7
    cr
    wcel
    @36
    @37
    wceq
    @34
    @7
    absresq
    syl
    @22
    @5
    @6
    @22
    cD
    @22
    cD
    @30
    recnd
    #
    sqrtcld
    @20
    @6
    cc
    wcel
    @17
    @14
    @20
    @6
    @32
    recnd
    ad2antlr
    sqmuld
    @22
    @38
    cD
    @11
    cmul
    @22
    cD
    @39
    sqsqrtd
    oveq1d
    3eqtrd
    @22
    @12
    @10
    clt
    wbr
    cc0
    @13
    clt
    wbr
    @22
    cc0
    c1
    @13
    clt
    0lt1
    @21
    @14
    simpr
    syl5breqr
    @22
    @12
    @10
    @22
    cD
    @11
    @30
    @22
    @6
    @33
    resqcld
    remulcld
    @22
    @4
    @20
    @4
    cr
    wcel
    #
    @17
    @14
    @18
    @40
    @19
    @4
    nn0re
    adantr
    ad2antlr
    #
    resqcld
    posdifd
    mpbird
    eqbrtrd
    @22
    @27
    @4
    @22
    @7
    @35
    abscld
    @41
    @22
    @7
    @35
    absge0d
    @20
    cc0
    @4
    cle
    wbr
    #
    @17
    @14
    @18
    @42
    @19
    @4
    nn0ge0
    adantr
    ad2antlr
    lt2sqd
    mpbird
    eqbrtrd
    @22
    cc0
    @7
    @4
    @22
    0red
    @34
    @41
    absdifltd
    mpbid
    simprd
    @22
    @4
    @7
    @20
    @4
    cc
    wcel
    #
    @17
    @14
    @18
    @43
    @19
    @4
    nn0cn
    adantr
    ad2antlr
    @35
    addcomd
    breqtrrd
    adantrl
    @21
    @9
    @14
    simprl
    breqtrrd
    ex
    rexlimdvva
    expimpd
    sylbid
    imp
end
