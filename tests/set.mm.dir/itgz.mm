include "cc0.mm"
include "citg.mm"
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
include "cc.mm"
include "cn0.mm"
include "ax-icn.mm"
include "elfznn0.mm"
include "expcl.mm"
include "sylancr.mm"
include "cz.mm"
include "wne.mm"
include "elfzelz.mm"
include "ine0.mm"
include "expne0i.mm"
include "mp3an12.mm"
include "syl.mm"
include "div0d.mm"
include "fveq2d.mm"
include "re0.mm"
include "syl6eq.mm"
include "ifeq1d.mm"
include "ifid.mm"
include "mpteq2dv.mm"
include "fconstmpt.mm"
include "syl6eqr.mm"
include "itg20.mm"
include "oveq2d.mm"
include "mul01d.mm"
include "eqtrd.mm"
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
include "3eqtri.mm"

theorem itgz
  let vx: setvar x
  let cA: class A
  let vk: setvar k
  let cB: class B
  let cC: class C


  assert |- S. A 0 _d x = 0

  proof
    vx
    cA
    cc0
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
    cA
    wcel
    cc0
    cc0
    @2
    cdiv
    co
    #
    cre
    cfv
    #
    cle
    wbr
    wa
    #
    @4
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
    @0
    cc0
    vk
    csu
    #
    cc0
    vx
    cA
    cc0
    @4
    vk
    @4
    eqid
    dfitg
    @0
    @9
    cc0
    vk
    @1
    @0
    wcel
    #
    @9
    @2
    cc0
    cmul
    co
    cc0
    @11
    @8
    cc0
    @2
    cmul
    @11
    @8
    cr
    cc0
    csn
    cxp
    #
    citg2
    cfv
    cc0
    @11
    @7
    @12
    citg2
    @11
    @7
    vx
    cr
    cc0
    cmpt
    @12
    @11
    vx
    cr
    @6
    cc0
    @11
    @6
    @5
    cc0
    cc0
    cif
    cc0
    @11
    @5
    @4
    cc0
    cc0
    @11
    @4
    cc0
    cre
    cfv
    cc0
    @11
    @3
    cc0
    cre
    @11
    @2
    @11
    ci
    cc
    wcel
    #
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
    #
    @11
    @1
    cz
    wcel
    #
    @2
    cc0
    wne
    #
    @1
    cc0
    c3
    elfzelz
    @13
    ci
    cc0
    wne
    @15
    @16
    ax-icn
    ine0
    ci
    @1
    expne0i
    mp3an12
    syl
    div0d
    fveq2d
    re0
    syl6eq
    ifeq1d
    @5
    cc0
    ifid
    syl6eq
    mpteq2dv
    vx
    cr
    cc0
    fconstmpt
    syl6eqr
    fveq2d
    itg20
    syl6eq
    oveq2d
    @11
    @2
    @14
    mul01d
    eqtrd
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
    @10
    cc0
    wceq
    @18
    @17
    cc0
    c3
    fzfi
    olci
    @0
    vk
    cc0
    sumz
    ax-mp
    3eqtri
end
