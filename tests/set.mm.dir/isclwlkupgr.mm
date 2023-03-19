include "cclwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cwlks.mm"
include "cc0.mm"
include "chash.mm"
include "wceq.mm"
include "wa.mm"
include "cupgr.mm"
include "wcel.mm"
include "cdm.mm"
include "cword.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "cfzo.mm"
include "wral.mm"
include "isclwlk.mm"
include "w3a.mm"
include "upgriswlk.mm"
include "anbi1d.mm"
include "3an4anass.mm"
include "syl6bb.mm"
include "syl5bb.mm"

theorem isclwlkupgr
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  assume isclwlke.v: |- V = ( Vtx ` G )
  assume isclwlke.i: |- I = ( iEdg ` G )

  disjoint F k
  disjoint G k
  disjoint P k
  disjoint I k
  disjoint V k
  assert |- ( G e. UPGraph -> ( F ( ClWalks ` G ) P <-> ( ( F e. Word dom I /\ P : ( 0 ... ( # ` F ) ) --> V ) /\ ( A. k e. ( 0 ..^ ( # ` F ) ) ( I ` ( F ` k ) ) = { ( P ` k ) , ( P ` ( k + 1 ) ) } /\ ( P ` 0 ) = ( P ` ( # ` F ) ) ) ) ) )

  proof
    cF
    cP
    cG
    cclwlks
    cfv
    wbr
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cc0
    cP
    cfv
    cF
    chash
    cfv
    #
    cP
    cfv
    wceq
    #
    wa
    #
    cG
    cupgr
    wcel
    #
    cF
    cI
    cdm
    cword
    wcel
    #
    cc0
    @1
    cfz
    co
    cV
    cP
    wf
    #
    wa
    vk
    cv
    #
    cF
    cfv
    cI
    cfv
    @7
    cP
    cfv
    @7
    c1
    caddc
    co
    cP
    cfv
    cpr
    wceq
    vk
    cc0
    @1
    cfzo
    co
    wral
    #
    @2
    wa
    wa
    #
    cP
    cF
    cG
    isclwlk
    @4
    @3
    @5
    @6
    @8
    w3a
    #
    @2
    wa
    @9
    @4
    @0
    @10
    @2
    cP
    vk
    cF
    cG
    cI
    cV
    isclwlke.v
    isclwlke.i
    upgriswlk
    anbi1d
    @5
    @6
    @8
    @2
    3an4anass
    syl6bb
    syl5bb
end
