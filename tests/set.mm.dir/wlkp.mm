include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "ciedg.mm"
include "cdm.mm"
include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
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
include "simp2d.mm"

theorem wlkp
  let cP: class P
  let cF: class F
  let cG: class G
  let cV: class V
  let vk: setvar k
  assume wlkp.v: |- V = ( Vtx ` G )


  assert |- ( F ( Walks ` G ) P -> P : ( 0 ... ( # ` F ) ) --> V )

  proof
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    cF
    cG
    ciedg
    cfv
    #
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
    cV
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
    @0
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
    @1
    cfzo
    co
    wral
    cP
    vk
    cF
    cG
    @0
    cV
    wlkp.v
    @0
    eqid
    wlkprop
    simp2d
end
