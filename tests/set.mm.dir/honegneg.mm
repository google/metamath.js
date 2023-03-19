include "chil.mm"
include "wf.mm"
include "c1.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "chot.mm"
include "neg1mulneg1e1.mm"
include "oveq1i.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "neg1cn.mm"
include "homulass.mm"
include "mp3an12.mm"
include "homulid2.mm"
include "3eqtr3a.mm"

theorem honegneg
  let cT: class T


  assert |- ( T : ~H --> ~H -> ( -u 1 .op ( -u 1 .op T ) ) = T )

  proof
    chil
    chil
    cT
    wf
    #
    c1
    cneg
    #
    @1
    cmul
    co
    #
    cT
    chot
    co
    #
    c1
    cT
    chot
    co
    @1
    @1
    cT
    chot
    co
    chot
    co
    #
    cT
    @2
    c1
    cT
    chot
    neg1mulneg1e1
    oveq1i
    @1
    cc
    wcel
    #
    @5
    @0
    @3
    @4
    wceq
    neg1cn
    neg1cn
    @1
    @1
    cT
    homulass
    mp3an12
    cT
    homulid2
    3eqtr3a
end
