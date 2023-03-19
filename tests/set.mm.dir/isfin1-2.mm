include "cfn.mm"
include "wcel.mm"
include "cvv.mm"
include "cpw.mm"
include "cfin4.mm"
include "elex.mm"
include "pwexb.mm"
include "bitri.mm"
include "sylibr.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wn.mm"
include "ominf.mm"
include "pwfi.mm"
include "domfi.mm"
include "expcom.mm"
include "syl5bi.mm"
include "mtoi.mm"
include "fineqvlem.mm"
include "ex.mm"
include "impbid2.mm"
include "con2bid.mm"
include "wb.mm"
include "isfin4-2.mm"
include "sylbi.mm"
include "bitr4d.mm"
include "pm5.21nii.mm"

theorem isfin1-2
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cV: class V


  assert |- ( A e. Fin <-> ~P ~P A e. Fin4 )

  proof
    cA
    cfn
    wcel
    #
    cA
    cvv
    wcel
    #
    cA
    cpw
    #
    cpw
    #
    cfin4
    wcel
    #
    cA
    cfn
    elex
    @4
    @3
    cvv
    wcel
    #
    @1
    @3
    cfin4
    elex
    @1
    @2
    cvv
    wcel
    @5
    cA
    pwexb
    @2
    pwexb
    bitri
    #
    sylibr
    @1
    @0
    com
    @3
    cdom
    wbr
    #
    wn
    #
    @4
    @1
    @7
    @0
    @1
    @7
    @0
    wn
    #
    @7
    @0
    com
    cfn
    wcel
    #
    ominf
    @0
    @3
    cfn
    wcel
    #
    @7
    @10
    @0
    @2
    cfn
    wcel
    @11
    cA
    pwfi
    @2
    pwfi
    bitri
    @11
    @7
    @10
    @3
    com
    domfi
    expcom
    syl5bi
    mtoi
    @1
    @9
    @7
    cA
    cvv
    fineqvlem
    ex
    impbid2
    con2bid
    @1
    @5
    @4
    @8
    wb
    @6
    @3
    cvv
    isfin4-2
    sylbi
    bitr4d
    pm5.21nii
end
