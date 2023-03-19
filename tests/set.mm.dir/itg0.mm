include "c0.mm"
include "citg.mm"
include "cc0.mm"
include "c3.mm"
include "cfz.mm"
include "co.mm"
include "ci.mm"
include "cv.mm"
include "cexp.mm"
include "cr.mm"
include "wcel.mm"
include "cdiv.mm"
include "cre.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cif.mm"
include "cmpt.mm"
include "citg2.mm"
include "cmul.mm"
include "csu.mm"
include "eqid.mm"
include "dfitg.mm"
include "csn.mm"
include "cxp.mm"
include "ifan.mm"
include "noel.mm"
include "iffalsei.mm"
include "eqtri.mm"
include "mpteq2i.mm"
include "fconstmpt.mm"
include "eqtr4i.mm"
include "fveq2i.mm"
include "itg20.mm"
include "oveq2i.mm"
include "cc.mm"
include "cn0.mm"
include "ax-icn.mm"
include "elfznn0.mm"
include "expcl.mm"
include "sylancr.mm"
include "mul01d.mm"
include "syl5eq.mm"
include "sumeq2i.mm"
include "cuz.mm"
include "wss.mm"
include "cfn.mm"
include "wo.mm"
include "wceq.mm"
include "fzfi.mm"
include "olci.mm"
include "sumz.mm"
include "ax-mp.mm"

theorem itg0
  let vx: setvar x
  let cA: class A
  let vk: setvar k
  let cB: class B
  let cC: class C


  assert |- S. (/) A _d x = 0

  proof
    vx
    c0
    cA
    citg
    cc0
    c3
    cfz
    co
    #
    ci
    vk
    cv
    #
    cexp
    co
    #
    vx
    cr
    vx
    cv
    #
    c0
    wcel
    #
    cc0
    cA
    @2
    cdiv
    co
    cre
    cfv
    #
    cle
    wbr
    #
    wa
    @5
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cmul
    co
    #
    vk
    csu
    #
    cc0
    vx
    c0
    cA
    @5
    vk
    @5
    eqid
    dfitg
    @11
    @0
    cc0
    vk
    csu
    #
    cc0
    @0
    @10
    cc0
    vk
    @1
    @0
    wcel
    #
    @10
    @2
    cc0
    cmul
    co
    cc0
    @9
    cc0
    @2
    cmul
    @9
    cr
    cc0
    csn
    cxp
    #
    citg2
    cfv
    cc0
    @8
    @14
    citg2
    @8
    vx
    cr
    cc0
    cmpt
    @14
    vx
    cr
    @7
    cc0
    @7
    @4
    @6
    @5
    cc0
    cif
    #
    cc0
    cif
    cc0
    @4
    @6
    @5
    cc0
    ifan
    @4
    @15
    cc0
    @3
    noel
    iffalsei
    eqtri
    mpteq2i
    vx
    cr
    cc0
    fconstmpt
    eqtr4i
    fveq2i
    itg20
    eqtri
    oveq2i
    @13
    @2
    @13
    ci
    cc
    wcel
    @1
    cn0
    wcel
    @2
    cc
    wcel
    ax-icn
    @1
    c3
    elfznn0
    ci
    @1
    expcl
    sylancr
    mul01d
    syl5eq
    sumeq2i
    @0
    cc0
    cuz
    cfv
    wss
    #
    @0
    cfn
    wcel
    #
    wo
    @12
    cc0
    wceq
    @17
    @16
    cc0
    c3
    fzfi
    olci
    @0
    vk
    cc0
    sumz
    ax-mp
    eqtri
    eqtri
end
