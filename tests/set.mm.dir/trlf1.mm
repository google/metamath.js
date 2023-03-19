include "ctrls.mm"
include "cfv.mm"
include "wbr.mm"
include "cwlks.mm"
include "ccnv.mm"
include "wfun.mm"
include "wa.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "cdm.mm"
include "wf1.mm"
include "istrl.mm"
include "cword.mm"
include "wcel.mm"
include "wf.mm"
include "wi.mm"
include "wlkf.mm"
include "wrdf.mm"
include "df-f1.mm"
include "simplbi2.mm"
include "3syl.mm"
include "imp.mm"
include "sylbi.mm"

theorem trlf1
  let cP: class P
  let cF: class F
  let cG: class G
  let cI: class I
  assume trlf1.i: |- I = ( iEdg ` G )


  assert |- ( F ( Trails ` G ) P -> F : ( 0 ..^ ( # ` F ) ) -1-1-> dom I )

  proof
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cF
    ccnv
    wfun
    #
    wa
    cc0
    cF
    chash
    cfv
    cfzo
    co
    #
    cI
    cdm
    #
    cF
    wf1
    #
    cP
    cF
    cG
    istrl
    @0
    @1
    @4
    @0
    cF
    @3
    cword
    wcel
    @2
    @3
    cF
    wf
    #
    @1
    @4
    wi
    cP
    cF
    cG
    cI
    trlf1.i
    wlkf
    @3
    cF
    wrdf
    @4
    @5
    @1
    @2
    @3
    cF
    df-f1
    simplbi2
    3syl
    imp
    sylbi
end
