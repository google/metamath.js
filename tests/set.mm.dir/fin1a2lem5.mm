include "com.mm"
include "wcel.mm"
include "c2o.mm"
include "cv.mm"
include "comu.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "csuc.mm"
include "wn.mm"
include "crn.mm"
include "nneob.mm"
include "cfv.mm"
include "wfn.mm"
include "wb.mm"
include "wf1.mm"
include "fin1a2lem4.mm"
include "f1fn.mm"
include "ax-mp.mm"
include "fvelrnb.mm"
include "eqcom.mm"
include "fin1a2lem3.mm"
include "eqeq2d.mm"
include "syl5bb.mm"
include "rexbiia.mm"
include "bitri.mm"
include "notbii.mm"
include "3bitr4g.mm"

theorem fin1a2lem5
  let vx: setvar x
  let cA: class A
  let cE: class E
  let va: setvar a
  let vf: setvar f
  let vy: setvar y
  let vb: setvar b
  let cS: class S
  assume fin1a2lem.b: |- E = ( x e. _om |-> ( 2o .o x ) )


  assert |- ( A e. _om -> ( A e. ran E <-> -. suc A e. ran E ) )

  proof
    cA
    com
    wcel
    cA
    c2o
    va
    cv
    #
    comu
    co
    #
    wceq
    #
    va
    com
    wrex
    #
    cA
    csuc
    #
    @1
    wceq
    #
    va
    com
    wrex
    #
    wn
    cA
    cE
    crn
    #
    wcel
    #
    @4
    @7
    wcel
    #
    wn
    va
    cA
    nneob
    @8
    @0
    cE
    cfv
    #
    cA
    wceq
    #
    va
    com
    wrex
    #
    @3
    cE
    com
    wfn
    #
    @8
    @12
    wb
    com
    com
    cE
    wf1
    @13
    vx
    cE
    fin1a2lem.b
    fin1a2lem4
    com
    com
    cE
    f1fn
    ax-mp
    #
    va
    com
    cA
    cE
    fvelrnb
    ax-mp
    @11
    @2
    va
    com
    @11
    cA
    @10
    wceq
    @0
    com
    wcel
    #
    @2
    @10
    cA
    eqcom
    @15
    @10
    @1
    cA
    vx
    @0
    cE
    fin1a2lem.b
    fin1a2lem3
    #
    eqeq2d
    syl5bb
    rexbiia
    bitri
    @9
    @6
    @9
    @10
    @4
    wceq
    #
    va
    com
    wrex
    #
    @6
    @13
    @9
    @18
    wb
    @14
    va
    com
    @4
    cE
    fvelrnb
    ax-mp
    @17
    @5
    va
    com
    @17
    @4
    @10
    wceq
    @15
    @5
    @10
    @4
    eqcom
    @15
    @10
    @1
    @4
    @16
    eqeq2d
    syl5bb
    rexbiia
    bitri
    notbii
    3bitr4g
end
