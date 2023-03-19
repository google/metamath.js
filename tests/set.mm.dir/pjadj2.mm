include "cpjh.mm"
include "crn.mm"
include "wcel.mm"
include "cho.mm"
include "cado.mm"
include "cfv.mm"
include "wceq.mm"
include "elpjhmop.mm"
include "hmopadj.mm"
include "syl.mm"

theorem pjadj2
  let cT: class T


  assert |- ( T e. ran projh -> ( adjh ` T ) = T )

  proof
    cT
    cpjh
    crn
    wcel
    cT
    cho
    wcel
    cT
    cado
    cfv
    cT
    wceq
    cT
    elpjhmop
    cT
    hmopadj
    syl
end
