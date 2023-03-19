include "cupgr.mm"
include "wcel.mm"
include "ctrls.mm"
include "cfv.mm"
include "wbr.mm"
include "cdm.mm"
include "cword.mm"
include "ccnv.mm"
include "wfun.mm"
include "wa.mm"
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
include "wf1.mm"
include "upgristrl.mm"
include "wb.mm"
include "iswrdb.mm"
include "a1i.mm"
include "anbi1d.mm"
include "df-f1.mm"
include "syl6bbr.mm"
include "3anbi1d.mm"
include "bitrd.mm"

theorem upgrf1istrl
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let vf: setvar f
  let vp: setvar p
  assume upgrtrls.v: |- V = ( Vtx ` G )
  assume upgrtrls.i: |- I = ( iEdg ` G )

  disjoint G k
  disjoint I k
  disjoint V k
  disjoint F k
  disjoint P k
  disjoint G f
  disjoint G p
  disjoint f k
  disjoint f p
  disjoint k p
  disjoint I f
  disjoint I p
  disjoint V p
  assert |- ( G e. UPGraph -> ( F ( Trails ` G ) P <-> ( F : ( 0 ..^ ( # ` F ) ) -1-1-> dom I /\ P : ( 0 ... ( # ` F ) ) --> V /\ A. k e. ( 0 ..^ ( # ` F ) ) ( I ` ( F ` k ) ) = { ( P ` k ) , ( P ` ( k + 1 ) ) } ) ) )

  proof
    cG
    cupgr
    wcel
    #
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    cF
    cI
    cdm
    #
    cword
    wcel
    #
    cF
    ccnv
    wfun
    #
    wa
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
    @5
    cfzo
    co
    #
    wral
    #
    w3a
    @8
    @1
    cF
    wf1
    #
    @6
    @9
    w3a
    cP
    vk
    cF
    cG
    cI
    cV
    upgrtrls.v
    upgrtrls.i
    upgristrl
    @0
    @4
    @10
    @6
    @9
    @0
    @4
    @8
    @1
    cF
    wf
    #
    @3
    wa
    @10
    @0
    @2
    @11
    @3
    @2
    @11
    wb
    @0
    @1
    cF
    iswrdb
    a1i
    anbi1d
    @8
    @1
    cF
    df-f1
    syl6bbr
    3anbi1d
    bitrd
end
