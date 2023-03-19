include "cwlks.mm"
include "cfv.mm"
include "wcel.mm"
include "cvv.mm"
include "cxp.mm"
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
include "elfvex.mm"
include "c1st.mm"
include "c2nd.mm"
include "wbr.mm"
include "wlkcpr.mm"
include "wlkvv.mm"
include "sylbi.mm"
include "wa.mm"
include "wlkcomp.mm"
include "biimpcd.mm"
include "mp2and.mm"

theorem wlkcompim
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  assume wlkcomp.v: |- V = ( Vtx ` G )
  assume wlkcomp.i: |- I = ( iEdg ` G )
  assume wlkcomp.1: |- F = ( 1st ` W )
  assume wlkcomp.2: |- P = ( 2nd ` W )

  disjoint F k
  disjoint G k
  disjoint P k
  assert |- ( W e. ( Walks ` G ) -> ( F e. Word dom I /\ P : ( 0 ... ( # ` F ) ) --> V /\ A. k e. ( 0 ..^ ( # ` F ) ) if- ( ( P ` k ) = ( P ` ( k + 1 ) ) , ( I ` ( F ` k ) ) = { ( P ` k ) } , { ( P ` k ) , ( P ` ( k + 1 ) ) } C_ ( I ` ( F ` k ) ) ) ) )

  proof
    cW
    cG
    cwlks
    cfv
    #
    wcel
    #
    cG
    cvv
    wcel
    #
    cW
    cvv
    cvv
    cxp
    wcel
    #
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
    cV
    cP
    wf
    vk
    cv
    #
    cP
    cfv
    #
    @5
    c1
    caddc
    co
    cP
    cfv
    #
    wceq
    @5
    cF
    cfv
    cI
    cfv
    #
    @6
    csn
    wceq
    @6
    @7
    cpr
    @8
    wss
    wif
    vk
    cc0
    @4
    cfzo
    co
    wral
    w3a
    #
    cW
    cG
    cwlks
    elfvex
    @1
    cW
    c1st
    cfv
    cW
    c2nd
    cfv
    @0
    wbr
    @3
    cG
    cW
    wlkcpr
    cG
    cW
    wlkvv
    sylbi
    @2
    @3
    wa
    @1
    @9
    cP
    cvv
    cvv
    cvv
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
    wlkcomp
    biimpcd
    mp2and
end
