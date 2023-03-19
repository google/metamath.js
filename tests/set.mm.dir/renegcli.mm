include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wrex.mm"
include "cneg.mm"
include "ax-rnegex.mm"
include "cc.mm"
include "wb.mm"
include "recn.mm"
include "cmin.mm"
include "df-neg.mm"
include "eqeq1i.mm"
include "0cn.mm"
include "recni.mm"
include "subadd.mm"
include "mp3an12.mm"
include "syl5bb.mm"
include "syl.mm"
include "eleq1a.mm"
include "sylbird.mm"
include "rexlimiv.mm"
include "mp2b.mm"

theorem renegcli
  let cA: class A
  let vx: setvar x
  assume renegcl.1: |- A e. RR


  assert |- -u A e. RR

  proof
    cA
    cr
    wcel
    cA
    vx
    cv
    #
    caddc
    co
    cc0
    wceq
    #
    vx
    cr
    wrex
    cA
    cneg
    #
    cr
    wcel
    #
    renegcl.1
    vx
    cA
    ax-rnegex
    @1
    @3
    vx
    cr
    @0
    cr
    wcel
    #
    @1
    @2
    @0
    wceq
    #
    @3
    @4
    @0
    cc
    wcel
    #
    @5
    @1
    wb
    @0
    recn
    @5
    cc0
    cA
    cmin
    co
    #
    @0
    wceq
    #
    @6
    @1
    @2
    @7
    @0
    cA
    df-neg
    eqeq1i
    cc0
    cc
    wcel
    cA
    cc
    wcel
    @6
    @8
    @1
    wb
    0cn
    cA
    renegcl.1
    recni
    cc0
    cA
    @0
    subadd
    mp3an12
    syl5bb
    syl
    @0
    cr
    @2
    eleq1a
    sylbird
    rexlimiv
    mp2b
end
