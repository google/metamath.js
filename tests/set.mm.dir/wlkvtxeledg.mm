include "cvv.mm"
include "wcel.mm"
include "w3a.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cpr.mm"
include "wss.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "wral.mm"
include "wlkv.mm"
include "cdm.mm"
include "cword.mm"
include "cfz.mm"
include "cvtx.mm"
include "wf.mm"
include "wceq.mm"
include "csn.mm"
include "wif.mm"
include "eqid.mm"
include "iswlk.mm"
include "ifpsnprss.mm"
include "ralimi.mm"
include "3ad2ant3.mm"
include "syl6bi.mm"
include "mpcom.mm"

theorem wlkvtxeledg
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  assume wlkvtxeledg.i: |- I = ( iEdg ` G )

  disjoint G k
  disjoint F k
  disjoint P k
  assert |- ( F ( Walks ` G ) P -> A. k e. ( 0 ..^ ( # ` F ) ) { ( P ` k ) , ( P ` ( k + 1 ) ) } C_ ( I ` ( F ` k ) ) )

  proof
    cG
    cvv
    wcel
    cF
    cvv
    wcel
    cP
    cvv
    wcel
    w3a
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
    cpr
    @2
    cF
    cfv
    cI
    cfv
    #
    wss
    #
    vk
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    cP
    cF
    cG
    wlkv
    @0
    @1
    cF
    cI
    cdm
    cword
    wcel
    #
    cc0
    @7
    cfz
    co
    cG
    cvtx
    cfv
    #
    cP
    wf
    #
    @3
    @4
    wceq
    @5
    @3
    csn
    wceq
    @6
    wif
    #
    vk
    @8
    wral
    #
    w3a
    @9
    cP
    cvv
    vk
    cF
    cG
    cI
    @11
    cvv
    cvv
    @11
    eqid
    wlkvtxeledg.i
    iswlk
    @14
    @10
    @9
    @12
    @13
    @6
    vk
    @8
    @3
    @4
    @5
    ifpsnprss
    ralimi
    3ad2ant3
    syl6bi
    mpcom
end
