include "cray.mm"
include "wfun.mm"
include "cv.mm"
include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cop.mm"
include "coutsideof.mm"
include "wbr.mm"
include "crab.mm"
include "wceq.mm"
include "wa.mm"
include "cn.mm"
include "wrex.mm"
include "coprab.mm"
include "wmo.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "reeanv.mm"
include "simp1.mm"
include "axdimuniq.mm"
include "fveq2.mm"
include "rabeq.mm"
include "syl.mm"
include "eqeq2d.mm"
include "anbi1d.mm"
include "eqtr3.mm"
include "syl6bi.mm"
include "an4s.mm"
include "ex.mm"
include "com3l.mm"
include "syl2an.mm"
include "imp.mm"
include "com12.mm"
include "rexlimivv.mm"
include "sylbir.mm"
include "gen2.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "eleq2d.mm"
include "3anbi12d.mm"
include "anbi12d.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "mo4.mm"
include "mpbir.mm"
include "funoprab.mm"
include "df-ray.mm"
include "funeqi.mm"

theorem funray
  let va: setvar a
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vr: setvar r
  let vs: setvar s
  let vx: setvar x


  assert |- Fun Ray

  proof
    cray
    wfun
    vp
    cv
    #
    vn
    cv
    #
    cee
    cfv
    #
    wcel
    #
    va
    cv
    #
    @2
    wcel
    #
    @0
    @4
    wne
    #
    w3a
    #
    vr
    cv
    #
    @0
    @4
    vx
    cv
    cop
    coutsideof
    wbr
    #
    vx
    @2
    crab
    #
    wceq
    #
    wa
    #
    vn
    cn
    wrex
    #
    vp
    va
    vr
    coprab
    #
    wfun
    @13
    vp
    va
    vr
    @13
    vr
    wmo
    @13
    @0
    vm
    cv
    #
    cee
    cfv
    #
    wcel
    #
    @4
    @16
    wcel
    #
    @6
    w3a
    #
    vs
    cv
    #
    @9
    vx
    @16
    crab
    #
    wceq
    #
    wa
    #
    vm
    cn
    wrex
    #
    wa
    #
    vr
    vs
    weq
    #
    wi
    #
    vs
    wal
    vr
    wal
    @27
    vr
    vs
    @25
    @12
    @23
    wa
    #
    vm
    cn
    wrex
    vn
    cn
    wrex
    @26
    @12
    @23
    vn
    vm
    cn
    cn
    reeanv
    @28
    @26
    vn
    vm
    cn
    cn
    @28
    @1
    cn
    wcel
    #
    @15
    cn
    wcel
    #
    wa
    #
    @26
    @7
    @19
    @11
    @22
    @31
    @26
    wi
    #
    @7
    @19
    wa
    @11
    @22
    wa
    #
    @32
    @7
    @3
    @17
    @33
    @32
    wi
    @19
    @3
    @5
    @6
    simp1
    @17
    @18
    @6
    simp1
    @31
    @3
    @17
    wa
    #
    @33
    @26
    @31
    @34
    @33
    @26
    wi
    #
    @29
    @3
    @30
    @17
    @35
    @29
    @3
    wa
    @30
    @17
    wa
    wa
    vn
    vm
    weq
    #
    @35
    @0
    @15
    @1
    axdimuniq
    @36
    @33
    @8
    @21
    wceq
    #
    @22
    wa
    @26
    @36
    @11
    @37
    @22
    @36
    @10
    @21
    @8
    @36
    @2
    @16
    wceq
    @10
    @21
    wceq
    @1
    @15
    cee
    fveq2
    #
    @9
    vx
    @2
    @16
    rabeq
    syl
    #
    eqeq2d
    anbi1d
    @8
    @20
    @21
    eqtr3
    syl6bi
    syl
    an4s
    ex
    com3l
    syl2an
    imp
    an4s
    com12
    rexlimivv
    sylbir
    gen2
    @13
    @24
    vr
    vs
    @26
    @13
    @7
    @20
    @10
    wceq
    #
    wa
    #
    vn
    cn
    wrex
    @24
    @26
    @12
    @41
    vn
    cn
    @26
    @11
    @40
    @7
    @8
    @20
    @10
    eqeq1
    anbi2d
    rexbidv
    @41
    @23
    vn
    vm
    cn
    @36
    @7
    @19
    @40
    @22
    @36
    @3
    @17
    @5
    @18
    @6
    @36
    @2
    @16
    @0
    @38
    eleq2d
    @36
    @2
    @16
    @4
    @38
    eleq2d
    3anbi12d
    @36
    @10
    @21
    @20
    @39
    eqeq2d
    anbi12d
    cbvrexv
    syl6bb
    mo4
    mpbir
    funoprab
    cray
    @14
    vx
    vn
    vr
    vp
    va
    df-ray
    funeqi
    mpbir
end
