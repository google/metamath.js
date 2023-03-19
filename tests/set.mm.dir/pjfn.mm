include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "cpjh.mm"
include "cfv.mm"
include "wf.mm"
include "wfn.mm"
include "pjhf.mm"
include "ffn.mm"
include "syl.mm"

theorem pjfn
  let cH: class H


  assert |- ( H e. CH -> ( projh ` H ) Fn ~H )

  proof
    cH
    cch
    wcel
    chil
    chil
    cH
    cpjh
    cfv
    #
    wf
    @0
    chil
    wfn
    cH
    pjhf
    chil
    chil
    @0
    ffn
    syl
end
