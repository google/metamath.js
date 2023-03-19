include "clsxlim.mm"
include "wrel.mm"
include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "clm.mm"
include "lmrel.mm"
include "df-xlim.mm"
include "releqi.mm"
include "mpbir.mm"

theorem xlimrel
  let vk: setvar k
  let vx: setvar x


  assert |- Rel ~~>*

  proof
    clsxlim
    wrel
    cle
    cordt
    cfv
    #
    clm
    cfv
    #
    wrel
    @0
    lmrel
    clsxlim
    @1
    df-xlim
    releqi
    mpbir
end
