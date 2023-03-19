include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cdm.mm"
include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "cvtx.mm"
include "wf.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "csn.mm"
include "cpr.mm"
include "wss.mm"
include "wif.mm"
include "cfzo.mm"
include "wral.mm"
include "eqid.mm"
include "wlkprop.mm"
include "simp1d.mm"

theorem wlkf
  let cP: class P
  let cF: class F
  let cG: class G
  let cI: class I
  let vk: setvar k
  assume wlkf.i: |- I = ( iEdg ` G )


  assert |- ( F ( Walks ` G ) P -> F e. Word dom I )

  proof
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    cF
    cI
    cdm
    cword
    wcel
    cc0
    cF
    chash
    cfv
    #
    cfz
    co
    cG
    cvtx
    cfv
    #
    cP
    wf
    vk
    cv
    #
    cP
    cfv
    #
    @2
    c1
    caddc
    co
    cP
    cfv
    #
    wceq
    @2
    cF
    cfv
    cI
    cfv
    #
    @3
    csn
    wceq
    @3
    @4
    cpr
    @5
    wss
    wif
    vk
    cc0
    @0
    cfzo
    co
    wral
    cP
    vk
    cF
    cG
    cI
    @1
    @1
    eqid
    wlkf.i
    wlkprop
    simp1d
end
