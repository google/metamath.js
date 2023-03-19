include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cword.mm"
include "wcel.mm"
include "wlkp.mm"
include "ffz0iswrd.mm"
include "syl.mm"

theorem wlkpwrd
  let cP: class P
  let cF: class F
  let cG: class G
  let cV: class V
  let vk: setvar k
  assume wlkp.v: |- V = ( Vtx ` G )


  assert |- ( F ( Walks ` G ) P -> P e. Word V )

  proof
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    cc0
    cF
    chash
    cfv
    #
    cfz
    co
    cV
    cP
    wf
    cP
    cV
    cword
    wcel
    cP
    cF
    cG
    cV
    wlkp.v
    wlkp
    cV
    @0
    cP
    ffz0iswrd
    syl
end
