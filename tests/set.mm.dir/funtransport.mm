include "ctransport.mm"
include "wfun.mm"
include "cv.mm"
include "cee.mm"
include "cfv.mm"
include "cxp.mm"
include "wcel.mm"
include "c1st.mm"
include "c2nd.mm"
include "wne.mm"
include "w3a.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "ccgr.mm"
include "wa.mm"
include "crio.mm"
include "wceq.mm"
include "cn.mm"
include "wrex.mm"
include "coprab.mm"
include "wmo.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "reeanv.mm"
include "simp1.mm"
include "anim12i.mm"
include "anim1i.mm"
include "an4s.mm"
include "xp1st.mm"
include "axdimuniq.mm"
include "fveq2.mm"
include "riotaeqdv.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "eqtr3.mm"
include "syl6bir.mm"
include "syl.mm"
include "ex.mm"
include "syl2ani.mm"
include "impd.mm"
include "syl5.mm"
include "rexlimivv.mm"
include "sylbir.mm"
include "gen2.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "sqxpeqd.mm"
include "eleq2d.mm"
include "3anbi12d.mm"
include "anbi12d.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "mo4.mm"
include "mpbir.mm"
include "funoprab.mm"
include "df-transport.mm"
include "funeqi.mm"

theorem funtransport
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y


  assert |- Fun TransportTo

  proof
    ctransport
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
    @2
    cxp
    #
    wcel
    #
    vq
    cv
    #
    @3
    wcel
    #
    @5
    c1st
    cfv
    #
    @5
    c2nd
    cfv
    #
    wne
    #
    w3a
    #
    vx
    cv
    #
    @8
    @7
    vr
    cv
    #
    cop
    cbtwn
    wbr
    @8
    @12
    cop
    @0
    ccgr
    wbr
    wa
    #
    vr
    @2
    crio
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
    vq
    vx
    coprab
    #
    wfun
    @17
    vp
    vq
    vx
    @17
    vx
    wmo
    @17
    @0
    vm
    cv
    #
    cee
    cfv
    #
    @20
    cxp
    #
    wcel
    #
    @5
    @21
    wcel
    #
    @9
    w3a
    #
    vy
    cv
    #
    @13
    vr
    @20
    crio
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
    vx
    vy
    weq
    #
    wi
    #
    vy
    wal
    vx
    wal
    @32
    vx
    vy
    @30
    @16
    @28
    wa
    #
    vm
    cn
    wrex
    vn
    cn
    wrex
    @31
    @16
    @28
    vn
    vm
    cn
    cn
    reeanv
    @33
    @31
    vn
    vm
    cn
    cn
    @33
    @4
    @22
    wa
    #
    @15
    @27
    wa
    #
    wa
    #
    @1
    cn
    wcel
    #
    @19
    cn
    wcel
    #
    wa
    #
    @31
    @10
    @24
    @15
    @27
    @36
    @10
    @24
    wa
    @34
    @35
    @10
    @4
    @24
    @22
    @4
    @6
    @9
    simp1
    @22
    @23
    @9
    simp1
    anim12i
    anim1i
    an4s
    @39
    @34
    @35
    @31
    @4
    @39
    @0
    c1st
    cfv
    #
    @2
    wcel
    #
    @40
    @20
    wcel
    #
    @35
    @31
    wi
    #
    @22
    @0
    @2
    @2
    xp1st
    @0
    @20
    @20
    xp1st
    @39
    @41
    @42
    wa
    @43
    @37
    @41
    @38
    @42
    @43
    @37
    @41
    wa
    @38
    @42
    wa
    wa
    vn
    vm
    weq
    #
    @43
    @40
    @19
    @1
    axdimuniq
    @44
    @35
    @15
    @25
    @14
    wceq
    #
    wa
    @31
    @44
    @45
    @27
    @15
    @44
    @14
    @26
    @25
    @44
    @13
    vr
    @2
    @20
    @1
    @19
    cee
    fveq2
    #
    riotaeqdv
    eqeq2d
    #
    anbi2d
    @11
    @25
    @14
    eqtr3
    syl6bir
    syl
    an4s
    ex
    syl2ani
    impd
    syl5
    rexlimivv
    sylbir
    gen2
    @17
    @29
    vx
    vy
    @31
    @17
    @10
    @45
    wa
    #
    vn
    cn
    wrex
    @29
    @31
    @16
    @48
    vn
    cn
    @31
    @15
    @45
    @10
    @11
    @25
    @14
    eqeq1
    anbi2d
    rexbidv
    @48
    @28
    vn
    vm
    cn
    @44
    @10
    @24
    @45
    @27
    @44
    @4
    @22
    @6
    @23
    @9
    @44
    @3
    @21
    @0
    @44
    @2
    @20
    @46
    sqxpeqd
    #
    eleq2d
    @44
    @3
    @21
    @5
    @49
    eleq2d
    3anbi12d
    @47
    anbi12d
    cbvrexv
    syl6bb
    mo4
    mpbir
    funoprab
    ctransport
    @18
    vx
    vn
    vr
    vq
    vp
    df-transport
    funeqi
    mpbir
end
