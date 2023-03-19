include "cbo.mm"
include "cado.mm"
include "cdm.mm"
include "bdopssadj.mm"
include "sseli.mm"

theorem bdopadj
  let cT: class T


  assert |- ( T e. BndLinOp -> T e. dom adjh )

  proof
    cbo
    cado
    cdm
    cT
    bdopssadj
    sseli
end
