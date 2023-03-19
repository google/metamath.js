include "clsxlim.mm"
include "wbr.mm"
include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "cxr.mm"
include "ctopon.mm"
include "wcel.mm"
include "clm.mm"
include "letopon.mm"
include "df-xlim.mm"
include "breqi.mm"
include "biimpi.mm"
include "lmcl.mm"
include "sylancr.mm"

theorem xlimcl
  let cA: class A
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( F ~~>* A -> A e. RR* )

  proof
    cF
    cA
    clsxlim
    wbr
    #
    cle
    cordt
    cfv
    #
    cxr
    ctopon
    cfv
    wcel
    cF
    cA
    @1
    clm
    cfv
    #
    wbr
    #
    cA
    cxr
    wcel
    letopon
    @0
    @3
    cF
    cA
    clsxlim
    @2
    df-xlim
    breqi
    biimpi
    cA
    cF
    @1
    cxr
    lmcl
    sylancr
end
