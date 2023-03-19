include "cusgr.mm"
include "wcel.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "wf1.mm"
include "usgrexmplef.mm"
include "cvv.mm"
include "wb.mm"
include "cop.mm"
include "opex.mm"
include "eqeltri.mm"
include "ciedg.mm"
include "cvtx.mm"
include "eqid.mm"
include "isusgrs.mm"
include "wa.mm"
include "usgrexmpllem.mm"
include "simpr.mm"
include "dmeqd.mm"
include "pweq.mm"
include "adantr.mm"
include "rabeqdv.mm"
include "f1eq123d.mm"
include "ax-mp.mm"
include "syl6bb.mm"
include "mpbir.mm"

theorem usgrexmpl
  let cE: class E
  let cG: class G
  let cV: class V
  let ve: setvar e
  assume usgrexmpl.v: |- V = ( 0 ... 4 )
  assume usgrexmpl.e: |- E = <" { 0 , 1 } { 1 , 2 } { 2 , 0 } { 0 , 3 } ">
  assume usgrexmpl.g: |- G = <. V , E >.


  assert |- G e. USGraph

  proof
    cG
    cusgr
    wcel
    #
    cE
    cdm
    #
    ve
    cv
    chash
    cfv
    c2
    wceq
    #
    ve
    cV
    cpw
    #
    crab
    #
    cE
    wf1
    #
    ve
    cE
    cV
    usgrexmpl.v
    usgrexmpl.e
    usgrexmplef
    cG
    cvv
    wcel
    #
    @0
    @5
    wb
    cG
    cV
    cE
    cop
    cvv
    usgrexmpl.g
    cV
    cE
    opex
    eqeltri
    @6
    @0
    cG
    ciedg
    cfv
    #
    cdm
    #
    @2
    ve
    cG
    cvtx
    cfv
    #
    cpw
    #
    crab
    #
    @7
    wf1
    #
    @5
    ve
    cvv
    @7
    cG
    @9
    @9
    eqid
    @7
    eqid
    isusgrs
    @9
    cV
    wceq
    #
    @7
    cE
    wceq
    #
    wa
    #
    @12
    @5
    wb
    cE
    cG
    cV
    usgrexmpl.v
    usgrexmpl.e
    usgrexmpl.g
    usgrexmpllem
    @15
    @8
    @1
    @11
    @4
    @7
    cE
    @13
    @14
    simpr
    #
    @15
    @7
    cE
    @16
    dmeqd
    @15
    @2
    ve
    @10
    @3
    @13
    @10
    @3
    wceq
    @14
    @9
    cV
    pweq
    adantr
    rabeqdv
    f1eq123d
    ax-mp
    syl6bb
    ax-mp
    mpbir
end
