include "cline2.mm"
include "wfun.mm"
include "cv.mm"
include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cop.mm"
include "ccolin.mm"
include "ccnv.mm"
include "cec.mm"
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
include "eqtr3.mm"
include "ad2ant2l.mm"
include "a1i.mm"
include "rexlimivv.mm"
include "sylbir.mm"
include "gen2.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "3anbi12d.mm"
include "anbi1d.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "mo4.mm"
include "mpbir.mm"
include "funoprab.mm"
include "df-line2.mm"
include "funeqi.mm"

theorem funline
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  let vl: setvar l
  let vm: setvar m
  let vn: setvar n


  assert |- Fun Line

  proof
    cline2
    wfun
    va
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
    vb
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
    vl
    cv
    #
    @0
    @4
    cop
    ccolin
    ccnv
    cec
    #
    wceq
    #
    wa
    #
    vn
    cn
    wrex
    #
    va
    vb
    vl
    coprab
    #
    wfun
    @12
    va
    vb
    vl
    @12
    vl
    wmo
    @12
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
    @15
    wcel
    #
    @6
    w3a
    #
    vk
    cv
    #
    @9
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
    vl
    vk
    weq
    #
    wi
    #
    vk
    wal
    vl
    wal
    @25
    vl
    vk
    @23
    @11
    @21
    wa
    #
    vm
    cn
    wrex
    vn
    cn
    wrex
    @24
    @11
    @21
    vn
    vm
    cn
    cn
    reeanv
    @26
    @24
    vn
    vm
    cn
    cn
    @26
    @24
    wi
    @1
    cn
    wcel
    @14
    cn
    wcel
    wa
    @10
    @20
    @24
    @7
    @18
    @8
    @19
    @9
    eqtr3
    ad2ant2l
    a1i
    rexlimivv
    sylbir
    gen2
    @12
    @22
    vl
    vk
    @24
    @12
    @7
    @20
    wa
    #
    vn
    cn
    wrex
    @22
    @24
    @11
    @27
    vn
    cn
    @24
    @10
    @20
    @7
    @8
    @19
    @9
    eqeq1
    anbi2d
    rexbidv
    @27
    @21
    vn
    vm
    cn
    vn
    vm
    weq
    #
    @7
    @18
    @20
    @28
    @3
    @16
    @5
    @17
    @6
    @28
    @2
    @15
    @0
    @1
    @14
    cee
    fveq2
    #
    eleq2d
    @28
    @2
    @15
    @4
    @29
    eleq2d
    3anbi12d
    anbi1d
    cbvrexv
    syl6bb
    mo4
    mpbir
    funoprab
    cline2
    @13
    vn
    va
    vb
    vl
    df-line2
    funeqi
    mpbir
end
