include "wfun.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "copab.mm"
include "ccom.mm"
include "wmo.mm"
include "wal.mm"
include "funmo.mm"
include "alrimiv.mm"
include "moexexv.mm"
include "syl2anr.mm"
include "funopab.mm"
include "sylibr.mm"
include "df-co.mm"
include "funeqi.mm"

theorem funco
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( Fun F /\ Fun G ) -> Fun ( F o. G ) )

  proof
    cF
    wfun
    #
    cG
    wfun
    #
    wa
    #
    vx
    cv
    #
    vz
    cv
    #
    cG
    wbr
    #
    @4
    vy
    cv
    cF
    wbr
    #
    wa
    vz
    wex
    #
    vx
    vy
    copab
    #
    wfun
    #
    cF
    cG
    ccom
    #
    wfun
    @2
    @7
    vy
    wmo
    #
    vx
    wal
    @9
    @2
    @11
    vx
    @1
    @5
    vz
    wmo
    @6
    vy
    wmo
    #
    vz
    wal
    @11
    @0
    vz
    @3
    cG
    funmo
    @0
    @12
    vz
    vy
    @4
    cF
    funmo
    alrimiv
    @5
    @6
    vz
    vy
    moexexv
    syl2anr
    alrimiv
    @7
    vx
    vy
    funopab
    sylibr
    @10
    @8
    vx
    vy
    vz
    cF
    cG
    df-co
    funeqi
    sylibr
end
