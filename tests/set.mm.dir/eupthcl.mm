include "ceupth.mm"
include "cfv.mm"
include "wbr.mm"
include "cwlks.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "ciedg.mm"
include "cdm.mm"
include "wf1o.mm"
include "wa.mm"
include "cn0.mm"
include "wcel.mm"
include "eqid.mm"
include "eupthi.mm"
include "wlkcl.mm"
include "adantr.mm"
include "syl.mm"

theorem eupthcl
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( EulerPaths ` G ) P -> ( # ` F ) e. NN0 )

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
    #
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    cG
    ciedg
    cfv
    #
    cdm
    cF
    wf1o
    #
    wa
    @1
    cn0
    wcel
    #
    cP
    cF
    cG
    @2
    @2
    eqid
    eupthi
    @0
    @4
    @3
    cP
    cF
    cG
    wlkcl
    adantr
    syl
end
