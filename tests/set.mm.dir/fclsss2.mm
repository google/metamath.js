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
include "ccl.mm"
include "wral.mm"
include "simpl3.mm"
include "ssralv.mm"
include "syl.mm"
include "wb.mm"
include "simpl1.mm"
include "fclstopon.mm"
include "adantl.mm"
include "mpbid.mm"
include "isfcls2.mm"
include "syl2anc.mm"
include "simpl2.mm"
include "3imtr4d.mm"
include "ex.mm"
include "pm2.43d.mm"
include "ssrdv.mm"

theorem fclsss2
  let cF: class F
  let cG: class G
  let cJ: class J
  let cX: class X
  let vo: setvar o
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let cY: class Y


  assert |- ( ( J e. ( TopOn ` X ) /\ F e. ( Fil ` X ) /\ F C_ G ) -> ( J fClus G ) C_ ( J fClus F ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cF
    cX
    cfil
    cfv
    #
    wcel
    #
    cF
    cG
    wss
    #
    w3a
    #
    vx
    cJ
    cG
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
    vs
    cv
    cJ
    ccl
    cfv
    cfv
    wcel
    #
    vs
    cG
    wral
    #
    @11
    vs
    cF
    wral
    #
    @8
    @9
    @10
    @3
    @12
    @13
    wi
    @0
    @2
    @3
    @8
    simpl3
    @11
    vs
    cF
    cG
    ssralv
    syl
    @10
    @0
    cG
    @1
    wcel
    #
    @8
    @12
    wb
    @0
    @2
    @3
    @8
    simpl1
    #
    @10
    @0
    @14
    @15
    @8
    @0
    @14
    wb
    @4
    @7
    cG
    cJ
    cX
    fclstopon
    adantl
    mpbid
    @7
    cG
    cJ
    cX
    vs
    isfcls2
    syl2anc
    @10
    @0
    @2
    @9
    @13
    wb
    @15
    @0
    @2
    @3
    @8
    simpl2
    @7
    cF
    cJ
    cX
    vs
    isfcls2
    syl2anc
    3imtr4d
    ex
    pm2.43d
    ssrdv
end
