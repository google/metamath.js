include "cexid.mm"
include "wcel.mm"
include "csem.mm"
include "cin.mm"
include "cmndo.mm"
include "elinel2.mm"
include "df-mndo.mm"
include "eleq2s.mm"

theorem mndoisexid
  let cG: class G


  assert |- ( G e. MndOp -> G e. ExId )

  proof
    cG
    cexid
    wcel
    cG
    csem
    cexid
    cin
    cmndo
    cG
    csem
    cexid
    elinel2
    df-mndo
    eleq2s
end
