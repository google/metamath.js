include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cpr.mm"
include "wss.mm"
include "ciedg.mm"
include "crn.mm"
include "wrex.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "wral.mm"
include "eqid.mm"
include "wlkvtxiedg.mm"
include "cedg.mm"
include "edgval.mm"
include "eqtr2i.mm"
include "rexeqi.mm"
include "ralbii.mm"
include "sylib.mm"

theorem wlkvtxedg
  let cP: class P
  let ve: setvar e
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cG: class G
  assume wlkvtxedg.e: |- E = ( Edg ` G )

  disjoint E e
  disjoint F e
  disjoint F k
  disjoint e k
  disjoint G e
  disjoint G k
  disjoint P e
  disjoint P k
  assert |- ( F ( Walks ` G ) P -> A. k e. ( 0 ..^ ( # ` F ) ) E. e e. E { ( P ` k ) , ( P ` ( k + 1 ) ) } C_ e )

  proof
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    vk
    cv
    #
    cP
    cfv
    @0
    c1
    caddc
    co
    cP
    cfv
    cpr
    ve
    cv
    wss
    #
    ve
    cG
    ciedg
    cfv
    #
    crn
    #
    wrex
    #
    vk
    cc0
    cF
    chash
    cfv
    cfzo
    co
    #
    wral
    @1
    ve
    cE
    wrex
    #
    vk
    @5
    wral
    cP
    ve
    vk
    cF
    cG
    @2
    @2
    eqid
    wlkvtxiedg
    @4
    @6
    vk
    @5
    @1
    ve
    @3
    cE
    cE
    cG
    cedg
    cfv
    @3
    wlkvtxedg.e
    cG
    edgval
    eqtr2i
    rexeqi
    ralbii
    sylib
end
