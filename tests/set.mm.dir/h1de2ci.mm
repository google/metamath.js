include "csn.mm"
include "cort.mm"
include "cfv.mm"
include "wcel.mm"
include "chil.mm"
include "cv.mm"
include "csm.mm"
include "co.mm"
include "wceq.mm"
include "cc.mm"
include "wrex.mm"
include "wss.mm"
include "cch.mm"
include "snssi.mm"
include "occl.mm"
include "mp2b.mm"
include "choccli.mm"
include "cheli.mm"
include "hvmulcl.mm"
include "mpan2.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimiv.mm"
include "wb.mm"
include "c0v.mm"
include "cif.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "bibi12d.mm"
include "ifhvhv0.mm"
include "h1de2ctlem.mm"
include "dedth.mm"
include "pm5.21nii.mm"

theorem h1de2ci
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume h1de2ct.1: |- B e. ~H

  disjoint A x
  disjoint B x
  assert |- ( A e. ( _|_ ` ( _|_ ` { B } ) ) <-> E. x e. CC A = ( x .h B ) )

  proof
    cA
    cB
    csn
    #
    cort
    cfv
    #
    cort
    cfv
    #
    wcel
    #
    cA
    chil
    wcel
    #
    cA
    vx
    cv
    #
    cB
    csm
    co
    #
    wceq
    #
    vx
    cc
    wrex
    #
    cA
    @2
    @1
    cB
    chil
    wcel
    #
    @0
    chil
    wss
    @1
    cch
    wcel
    h1de2ct.1
    cB
    chil
    snssi
    @0
    occl
    mp2b
    choccli
    cheli
    @7
    @4
    vx
    cc
    @5
    cc
    wcel
    #
    @4
    @7
    @6
    chil
    wcel
    #
    @10
    @9
    @11
    h1de2ct.1
    @5
    cB
    hvmulcl
    mpan2
    cA
    @6
    chil
    eleq1
    syl5ibrcom
    rexlimiv
    @4
    @3
    @8
    wb
    @4
    cA
    c0v
    cif
    #
    @2
    wcel
    #
    @12
    @6
    wceq
    #
    vx
    cc
    wrex
    #
    wb
    cA
    c0v
    cA
    @12
    wceq
    #
    @3
    @13
    @8
    @15
    cA
    @12
    @2
    eleq1
    @16
    @7
    @14
    vx
    cc
    cA
    @12
    @6
    eqeq1
    rexbidv
    bibi12d
    vx
    @12
    cB
    cA
    ifhvhv0
    h1de2ct.1
    h1de2ctlem
    dedth
    pm5.21nii
end
