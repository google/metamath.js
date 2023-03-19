include "wrel.mm"
include "wa.mm"
include "cun.mm"
include "wfun.mm"
include "funrel.mm"
include "relun.mm"
include "sylib.mm"
include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "wal.mm"
include "simpl.mm"
include "fununmo.mm"
include "alrimiv.mm"
include "anim12i.mm"
include "dffun6.mm"
include "sylibr.mm"
include "simpr.mm"
include "uncom.mm"
include "funeqi.mm"
include "sylbi.mm"
include "jca.mm"
include "mpancom.mm"

theorem fununfun
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y


  assert |- ( Fun ( F u. G ) -> ( Fun F /\ Fun G ) )

  proof
    cF
    wrel
    #
    cG
    wrel
    #
    wa
    #
    cF
    cG
    cun
    #
    wfun
    #
    cF
    wfun
    #
    cG
    wfun
    #
    wa
    @4
    @3
    wrel
    @2
    @3
    funrel
    cF
    cG
    relun
    sylib
    @2
    @4
    wa
    #
    @5
    @6
    @7
    @0
    vx
    cv
    #
    vy
    cv
    #
    cF
    wbr
    vy
    wmo
    #
    vx
    wal
    #
    wa
    @5
    @2
    @0
    @4
    @11
    @0
    @1
    simpl
    @4
    @10
    vx
    vx
    vy
    cF
    cG
    fununmo
    alrimiv
    anim12i
    vx
    vy
    cF
    dffun6
    sylibr
    @7
    @1
    @8
    @9
    cG
    wbr
    vy
    wmo
    #
    vx
    wal
    #
    wa
    @6
    @2
    @1
    @4
    @13
    @0
    @1
    simpr
    @4
    @12
    vx
    @4
    cG
    cF
    cun
    #
    wfun
    @12
    @3
    @14
    cF
    cG
    uncom
    funeqi
    vx
    vy
    cG
    cF
    fununmo
    sylbi
    alrimiv
    anim12i
    vx
    vy
    cG
    dffun6
    sylibr
    jca
    mpancom
end
