include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cfil.mm"
include "wss.mm"
include "w3a.mm"
include "cfcls.mm"
include "co.mm"
include "cv.mm"
include "wi.mm"
include "wa.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "simpl3.mm"
include "ssralv.mm"
include "anim2d.mm"
include "syl.mm"
include "wb.mm"
include "simpl2.mm"
include "fclstopon.mm"
include "adantl.mm"
include "mpbird.mm"
include "fclsopn.mm"
include "syl2anc.mm"
include "simpl1.mm"
include "3imtr4d.mm"
include "ex.mm"
include "pm2.43d.mm"
include "ssrdv.mm"

theorem fclsss1
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let vo: setvar o
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cG: class G
  let cY: class Y


  assert |- ( ( J e. ( TopOn ` X ) /\ F e. ( Fil ` X ) /\ J C_ K ) -> ( K fClus F ) C_ ( J fClus F ) )

  proof
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    #
    cF
    cX
    cfil
    cfv
    wcel
    #
    cJ
    cK
    wss
    #
    w3a
    #
    vx
    cK
    cF
    cfcls
    co
    #
    cJ
    cF
    cfcls
    co
    #
    @4
    vx
    cv
    #
    @5
    wcel
    #
    @7
    @6
    wcel
    #
    @4
    @8
    @8
    @9
    wi
    @4
    @8
    wa
    #
    @7
    cX
    wcel
    #
    @7
    vo
    cv
    #
    wcel
    @12
    vs
    cv
    cin
    c0
    wne
    vs
    cF
    wral
    wi
    #
    vo
    cK
    wral
    #
    wa
    #
    @11
    @13
    vo
    cJ
    wral
    #
    wa
    #
    @8
    @9
    @10
    @3
    @15
    @17
    wi
    @1
    @2
    @3
    @8
    simpl3
    @3
    @14
    @16
    @11
    @13
    vo
    cJ
    cK
    ssralv
    anim2d
    syl
    @10
    cK
    @0
    wcel
    #
    @2
    @8
    @15
    wb
    @10
    @18
    @2
    @1
    @2
    @3
    @8
    simpl2
    #
    @8
    @18
    @2
    wb
    @4
    @7
    cF
    cK
    cX
    fclstopon
    adantl
    mpbird
    @19
    @7
    vo
    cF
    cK
    cX
    vs
    fclsopn
    syl2anc
    @10
    @1
    @2
    @9
    @17
    wb
    @1
    @2
    @3
    @8
    simpl1
    @19
    @7
    vo
    cF
    cJ
    cX
    vs
    fclsopn
    syl2anc
    3imtr4d
    ex
    pm2.43d
    ssrdv
end
