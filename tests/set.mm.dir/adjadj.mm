include "cado.mm"
include "cdm.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "w3a.mm"
include "adj2.mm"
include "dmadjrn.mm"
include "adj1.mm"
include "syl3an1.mm"
include "eqtr2d.mm"
include "3expib.mm"
include "ralrimivv.mm"
include "wf.mm"
include "wb.mm"
include "dmadjop.mm"
include "3syl.mm"
include "hoeq1.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem adjadj
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S


  assert |- ( T e. dom adjh -> ( adjh ` ( adjh ` T ) ) = T )

  proof
    cT
    cado
    cdm
    #
    wcel
    #
    vx
    cv
    #
    cT
    cado
    cfv
    #
    cado
    cfv
    #
    cfv
    vy
    cv
    #
    csp
    co
    #
    @2
    cT
    cfv
    @5
    csp
    co
    #
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    #
    @4
    cT
    wceq
    #
    @1
    @8
    vx
    vy
    chil
    chil
    @1
    @2
    chil
    wcel
    #
    @5
    chil
    wcel
    #
    @8
    @1
    @11
    @12
    w3a
    @7
    @2
    @5
    @3
    cfv
    csp
    co
    #
    @6
    @2
    @5
    cT
    adj2
    @1
    @3
    @0
    wcel
    #
    @11
    @12
    @13
    @6
    wceq
    cT
    dmadjrn
    #
    @2
    @5
    @3
    adj1
    syl3an1
    eqtr2d
    3expib
    ralrimivv
    @1
    chil
    chil
    @4
    wf
    #
    chil
    chil
    cT
    wf
    @9
    @10
    wb
    @1
    @14
    @4
    @0
    wcel
    @16
    @15
    @3
    dmadjrn
    @4
    dmadjop
    3syl
    cT
    dmadjop
    vx
    vy
    @4
    cT
    hoeq1
    syl2anc
    mpbid
end
