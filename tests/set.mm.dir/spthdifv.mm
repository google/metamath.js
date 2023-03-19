include "cspths.mm"
include "cfv.mm"
include "wbr.mm"
include "ctrls.mm"
include "ccnv.mm"
include "wfun.mm"
include "wa.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "cvtx.mm"
include "wf1.mm"
include "isspth.mm"
include "cwlks.mm"
include "wf.mm"
include "wi.mm"
include "trliswlk.mm"
include "eqid.mm"
include "wlkp.mm"
include "df-f1.mm"
include "simplbi2.mm"
include "3syl.mm"
include "imp.mm"
include "sylbi.mm"

theorem spthdifv
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( SPaths ` G ) P -> P : ( 0 ... ( # ` F ) ) -1-1-> ( Vtx ` G ) )

  proof
    cF
    cP
    cG
    cspths
    cfv
    wbr
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    #
    cP
    ccnv
    wfun
    #
    wa
    cc0
    cF
    chash
    cfv
    cfz
    co
    #
    cG
    cvtx
    cfv
    #
    cP
    wf1
    #
    cP
    cF
    cG
    isspth
    @0
    @1
    @4
    @0
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    @2
    @3
    cP
    wf
    #
    @1
    @4
    wi
    cP
    cF
    cG
    trliswlk
    cP
    cF
    cG
    @3
    @3
    eqid
    wlkp
    @4
    @5
    @1
    @2
    @3
    cP
    df-f1
    simplbi2
    3syl
    imp
    sylbi
end
