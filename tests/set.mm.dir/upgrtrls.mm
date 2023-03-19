include "cupgr.mm"
include "wcel.mm"
include "ctrls.mm"
include "cfv.mm"
include "cv.mm"
include "cwlks.mm"
include "wbr.mm"
include "ccnv.mm"
include "wfun.mm"
include "wa.mm"
include "copab.mm"
include "cdm.mm"
include "cword.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "wceq.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "trlsfval.mm"
include "upgriswlk.mm"
include "anbi1d.mm"
include "an32.mm"
include "3anass.mm"
include "anbi1i.mm"
include "3bitr4i.mm"
include "syl6bb.mm"
include "opabbidv.mm"
include "syl5eq.mm"

theorem upgrtrls
  let vf: setvar f
  let vk: setvar k
  let cG: class G
  let cI: class I
  let cV: class V
  let vp: setvar p
  assume upgrtrls.v: |- V = ( Vtx ` G )
  assume upgrtrls.i: |- I = ( iEdg ` G )

  disjoint G f
  disjoint G k
  disjoint G p
  disjoint f k
  disjoint f p
  disjoint k p
  disjoint I f
  disjoint I k
  disjoint I p
  disjoint V k
  disjoint V p
  assert |- ( G e. UPGraph -> ( Trails ` G ) = { <. f , p >. | ( ( f e. Word dom I /\ Fun `' f ) /\ p : ( 0 ... ( # ` f ) ) --> V /\ A. k e. ( 0 ..^ ( # ` f ) ) ( I ` ( f ` k ) ) = { ( p ` k ) , ( p ` ( k + 1 ) ) } ) } )

  proof
    cG
    cupgr
    wcel
    #
    cG
    ctrls
    cfv
    vf
    cv
    #
    vp
    cv
    #
    cG
    cwlks
    cfv
    wbr
    #
    @1
    ccnv
    wfun
    #
    wa
    #
    vf
    vp
    copab
    @1
    cI
    cdm
    cword
    wcel
    #
    @4
    wa
    #
    cc0
    @1
    chash
    cfv
    #
    cfz
    co
    cV
    @2
    wf
    #
    vk
    cv
    #
    @1
    cfv
    cI
    cfv
    @10
    @2
    cfv
    @10
    c1
    caddc
    co
    @2
    cfv
    cpr
    wceq
    vk
    cc0
    @8
    cfzo
    co
    wral
    #
    w3a
    #
    vf
    vp
    copab
    vf
    cG
    vp
    trlsfval
    @0
    @5
    @12
    vf
    vp
    @0
    @5
    @6
    @9
    @11
    w3a
    #
    @4
    wa
    #
    @12
    @0
    @3
    @13
    @4
    @2
    vk
    @1
    cG
    cI
    cV
    upgrtrls.v
    upgrtrls.i
    upgriswlk
    anbi1d
    @6
    @9
    @11
    wa
    #
    wa
    #
    @4
    wa
    @7
    @15
    wa
    @14
    @12
    @6
    @15
    @4
    an32
    @13
    @16
    @4
    @6
    @9
    @11
    3anass
    anbi1i
    @7
    @9
    @11
    3anass
    3bitr4i
    syl6bb
    opabbidv
    syl5eq
end
