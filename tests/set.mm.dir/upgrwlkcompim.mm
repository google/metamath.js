include "cupgr.mm"
include "wcel.mm"
include "cwlks.mm"
include "cfv.mm"
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
include "cpr.mm"
include "wceq.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "wbr.mm"
include "c1st.mm"
include "c2nd.mm"
include "wlkcpr.mm"
include "breq12i.mm"
include "bitr4i.mm"
include "upgriswlk.mm"
include "biimpd.mm"
include "syl5bi.mm"
include "imp.mm"

theorem upgrwlkcompim
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  assume upgrwlkcompim.v: |- V = ( Vtx ` G )
  assume upgrwlkcompim.i: |- I = ( iEdg ` G )
  assume upgrwlkcompim.1: |- F = ( 1st ` W )
  assume upgrwlkcompim.2: |- P = ( 2nd ` W )

  disjoint F k
  disjoint G k
  disjoint I k
  disjoint P k
  disjoint V k
  assert |- ( ( G e. UPGraph /\ W e. ( Walks ` G ) ) -> ( F e. Word dom I /\ P : ( 0 ... ( # ` F ) ) --> V /\ A. k e. ( 0 ..^ ( # ` F ) ) ( I ` ( F ` k ) ) = { ( P ` k ) , ( P ` ( k + 1 ) ) } ) )

  proof
    cG
    cupgr
    wcel
    #
    cW
    cG
    cwlks
    cfv
    #
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
    cF
    cfv
    cI
    cfv
    @4
    cP
    cfv
    @4
    c1
    caddc
    co
    cP
    cfv
    cpr
    wceq
    vk
    cc0
    @3
    cfzo
    co
    wral
    w3a
    #
    @2
    cF
    cP
    @1
    wbr
    #
    @0
    @5
    @2
    cW
    c1st
    cfv
    #
    cW
    c2nd
    cfv
    #
    @1
    wbr
    @6
    cG
    cW
    wlkcpr
    cF
    @7
    cP
    @8
    @1
    upgrwlkcompim.1
    upgrwlkcompim.2
    breq12i
    bitr4i
    @0
    @6
    @5
    cP
    vk
    cF
    cG
    cI
    cV
    upgrwlkcompim.v
    upgrwlkcompim.i
    upgriswlk
    biimpd
    syl5bi
    imp
end
