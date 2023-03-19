include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "c2.mm"
include "cv.mm"
include "cexp.mm"
include "csu.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "cdiv.mm"
include "cz.mm"
include "wceq.mm"
include "nn0z.mm"
include "fzoval.mm"
include "syl.mm"
include "sumeq1d.mm"
include "cc.mm"
include "2cn.mm"
include "a1i.mm"
include "wne.mm"
include "1ne2.mm"
include "necomi.mm"
include "id.mm"
include "geoser.mm"
include "cneg.mm"
include "expcld.mm"
include "ax-1cn.mm"
include "subcld.mm"
include "ax-1ne0.mm"
include "div2negd.mm"
include "negsubdi2d.mm"
include "2m1e1.mm"
include "negeqi.mm"
include "negsubdi2i.mm"
include "eqtr3i.mm"
include "oveq12d.mm"
include "div1d.mm"
include "3eqtr3d.mm"
include "3eqtrd.mm"

theorem geo2sum2
  let vk: setvar k
  let cN: class N

  disjoint N k
  assert |- ( N e. NN0 -> sum_ k e. ( 0 ..^ N ) ( 2 ^ k ) = ( ( 2 ^ N ) - 1 ) )

  proof
    cN
    cn0
    wcel
    #
    cc0
    cN
    cfzo
    co
    #
    c2
    vk
    cv
    cexp
    co
    #
    vk
    csu
    cc0
    cN
    c1
    cmin
    co
    cfz
    co
    #
    @2
    vk
    csu
    c1
    c2
    cN
    cexp
    co
    #
    cmin
    co
    #
    c1
    c2
    cmin
    co
    #
    cdiv
    co
    #
    @4
    c1
    cmin
    co
    #
    @0
    @1
    @3
    @2
    vk
    @0
    cN
    cz
    wcel
    @1
    @3
    wceq
    cN
    nn0z
    cc0
    cN
    fzoval
    syl
    sumeq1d
    @0
    c2
    vk
    cN
    c2
    cc
    wcel
    @0
    2cn
    a1i
    #
    c2
    c1
    wne
    @0
    c1
    c2
    1ne2
    necomi
    a1i
    @0
    id
    #
    geoser
    @0
    @8
    cneg
    #
    c1
    cneg
    #
    cdiv
    co
    @8
    c1
    cdiv
    co
    @7
    @8
    @0
    @8
    c1
    @0
    @4
    c1
    @0
    c2
    cN
    @9
    @10
    expcld
    #
    c1
    cc
    wcel
    @0
    ax-1cn
    a1i
    #
    subcld
    #
    @14
    c1
    cc0
    wne
    @0
    ax-1ne0
    a1i
    div2negd
    @0
    @11
    @5
    @12
    @6
    cdiv
    @0
    @4
    c1
    @13
    @14
    negsubdi2d
    @12
    @6
    wceq
    @0
    c2
    c1
    cmin
    co
    #
    cneg
    @12
    @6
    @16
    c1
    2m1e1
    negeqi
    c2
    c1
    2cn
    ax-1cn
    negsubdi2i
    eqtr3i
    a1i
    oveq12d
    @0
    @8
    @15
    div1d
    3eqtr3d
    3eqtrd
end
