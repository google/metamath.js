include "chil.mm"
include "wf.mm"
include "cv.mm"
include "c1.mm"
include "chot.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "csm.mm"
include "cc.mm"
include "ax-1cn.mm"
include "homval.mm"
include "mp3an1.mm"
include "ffvelrn.mm"
include "ax-hvmulid.mm"
include "syl.mm"
include "eqtrd.mm"
include "ralrimiva.mm"
include "wb.mm"
include "homulcl.mm"
include "mpan.mm"
include "hoeq.mm"
include "mpancom.mm"
include "mpbid.mm"

theorem homulid2
  let cT: class T
  let cA: class A
  let vx: setvar x
  let cB: class B
  let cU: class U


  assert |- ( T : ~H --> ~H -> ( 1 .op T ) = T )

  proof
    chil
    chil
    cT
    wf
    #
    vx
    cv
    #
    c1
    cT
    chot
    co
    #
    cfv
    #
    @1
    cT
    cfv
    #
    wceq
    #
    vx
    chil
    wral
    #
    @2
    cT
    wceq
    #
    @0
    @5
    vx
    chil
    @0
    @1
    chil
    wcel
    #
    wa
    #
    @3
    c1
    @4
    csm
    co
    #
    @4
    c1
    cc
    wcel
    #
    @0
    @8
    @3
    @10
    wceq
    ax-1cn
    c1
    @1
    cT
    homval
    mp3an1
    @9
    @4
    chil
    wcel
    @10
    @4
    wceq
    chil
    chil
    @1
    cT
    ffvelrn
    @4
    ax-hvmulid
    syl
    eqtrd
    ralrimiva
    chil
    chil
    @2
    wf
    #
    @0
    @6
    @7
    wb
    @11
    @0
    @12
    ax-1cn
    c1
    cT
    homulcl
    mpan
    vx
    @2
    cT
    hoeq
    mpancom
    mpbid
end
