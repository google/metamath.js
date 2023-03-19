include "cupgr.mm"
include "wcel.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cpr.mm"
include "wceq.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "wral.mm"
include "cdm.mm"
include "cword.mm"
include "cfz.mm"
include "cvtx.mm"
include "wf.mm"
include "w3a.mm"
include "eqid.mm"
include "upgriswlk.mm"
include "simp3.mm"
include "syl6bi.mm"
include "imp.mm"

theorem upgrwlkedg
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  assume upgrwlkedg.i: |- I = ( iEdg ` G )

  disjoint F k
  disjoint G k
  disjoint I k
  disjoint P k
  assert |- ( ( G e. UPGraph /\ F ( Walks ` G ) P ) -> A. k e. ( 0 ..^ ( # ` F ) ) ( I ` ( F ` k ) ) = { ( P ` k ) , ( P ` ( k + 1 ) ) } )

  proof
    cG
    cupgr
    wcel
    #
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    vk
    cv
    #
    cF
    cfv
    cI
    cfv
    @2
    cP
    cfv
    @2
    c1
    caddc
    co
    cP
    cfv
    cpr
    wceq
    vk
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    wral
    #
    @0
    @1
    cF
    cI
    cdm
    cword
    wcel
    #
    cc0
    @3
    cfz
    co
    cG
    cvtx
    cfv
    #
    cP
    wf
    #
    @4
    w3a
    @4
    cP
    vk
    cF
    cG
    cI
    @6
    @6
    eqid
    upgrwlkedg.i
    upgriswlk
    @5
    @7
    @4
    simp3
    syl6bi
    imp
end
