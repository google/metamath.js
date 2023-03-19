include "ctrls.mm"
include "cfv.mm"
include "wbr.mm"
include "cwlks.mm"
include "ccnv.mm"
include "wfun.mm"
include "wa.mm"
include "cupgr.mm"
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
include "cpr.mm"
include "wceq.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "istrl.mm"
include "upgriswlk.mm"
include "anbi1d.mm"
include "an32.mm"
include "3anass.mm"
include "anbi1i.mm"
include "3bitr4i.mm"
include "syl6bb.mm"
include "syl5bb.mm"

theorem upgristrl
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
  assert |- ( G e. UPGraph -> ( F ( Trails ` G ) P <-> ( ( F e. Word dom I /\ Fun `' F ) /\ P : ( 0 ... ( # ` F ) ) --> V /\ A. k e. ( 0 ..^ ( # ` F ) ) ( I ` ( F ` k ) ) = { ( P ` k ) , ( P ` ( k + 1 ) ) } ) ) )

  proof
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cF
    ccnv
    wfun
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
    @1
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
    @8
    cP
    cfv
    @8
    c1
    caddc
    co
    cP
    cfv
    cpr
    wceq
    vk
    cc0
    @6
    cfzo
    co
    wral
    #
    w3a
    #
    cP
    cF
    cG
    istrl
    @3
    @2
    @4
    @7
    @9
    w3a
    #
    @1
    wa
    #
    @10
    @3
    @0
    @11
    @1
    cP
    vk
    cF
    cG
    cI
    cV
    upgrtrls.v
    upgrtrls.i
    upgriswlk
    anbi1d
    @4
    @7
    @9
    wa
    #
    wa
    #
    @1
    wa
    @5
    @13
    wa
    @12
    @10
    @4
    @13
    @1
    an32
    @11
    @14
    @1
    @4
    @7
    @9
    3anass
    anbi1i
    @5
    @7
    @9
    3anass
    3bitr4i
    syl6bb
    syl5bb
end
