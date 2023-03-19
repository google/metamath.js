include "cwlks.mm"
include "cfv.mm"
include "wcel.mm"
include "cdm.mm"
include "cword.mm"
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
include "w3a.mm"
include "wa.mm"
include "wlkcompim.mm"
include "3simpa.mm"
include "syl.mm"

theorem wlkelwrd
  let cP: class P
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  let vk: setvar k
  assume wlkcomp.v: |- V = ( Vtx ` G )
  assume wlkcomp.i: |- I = ( iEdg ` G )
  assume wlkcomp.1: |- F = ( 1st ` W )
  assume wlkcomp.2: |- P = ( 2nd ` W )


  assert |- ( W e. ( Walks ` G ) -> ( F e. Word dom I /\ P : ( 0 ... ( # ` F ) ) --> V ) )

  proof
    cW
    cG
    cwlks
    cfv
    wcel
    cF
    cI
    cdm
    cword
    wcel
    #
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
    #
    vk
    cv
    #
    cP
    cfv
    #
    @3
    c1
    caddc
    co
    cP
    cfv
    #
    wceq
    @3
    cF
    cfv
    cI
    cfv
    #
    @4
    csn
    wceq
    @4
    @5
    cpr
    @6
    wss
    wif
    vk
    cc0
    @1
    cfzo
    co
    wral
    #
    w3a
    @0
    @2
    wa
    cP
    vk
    cF
    cG
    cI
    cV
    cW
    wlkcomp.v
    wlkcomp.i
    wlkcomp.1
    wlkcomp.2
    wlkcompim
    @0
    @2
    @7
    3simpa
    syl
end
