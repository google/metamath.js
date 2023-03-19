include "ceupth.mm"
include "cfv.mm"
include "wbr.mm"
include "cwlks.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "cvtx.mm"
include "wf.mm"
include "eupthiswlk.mm"
include "eqid.mm"
include "wlkp.mm"
include "syl.mm"

theorem eupthpf
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( EulerPaths ` G ) P -> P : ( 0 ... ( # ` F ) ) --> ( Vtx ` G ) )

  proof
    cF
    cP
    cG
    ceupth
    cfv
    wbr
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
    cfz
    co
    cG
    cvtx
    cfv
    #
    cP
    wf
    cP
    cF
    cG
    eupthiswlk
    cP
    cF
    cG
    @0
    @0
    eqid
    wlkp
    syl
end
