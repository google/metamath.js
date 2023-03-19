include "cnlm.mm"
include "clvec.mm"
include "cnvc.mm"
include "df-nvc.mm"
include "elin2.mm"

theorem isnvc
  let cW: class W


  assert |- ( W e. NrmVec <-> ( W e. NrmMod /\ W e. LVec ) )

  proof
    cW
    cnlm
    clvec
    cnvc
    df-nvc
    elin2
end
