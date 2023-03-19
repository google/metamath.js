include "cv.mm"
include "cpw.mm"
include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "con0.mm"
include "wral.mm"
include "cale.mm"
include "cfv.mm"
include "wi.mm"
include "alephon.mm"
include "wceq.mm"
include "pweq.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "ax-mp.mm"
include "ralrimivw.mm"
include "com.mm"
include "wn.mm"
include "wss.mm"
include "wb.mm"
include "omelon.mm"
include "cardon.mm"
include "ontri1.mm"
include "mp2an.mm"
include "wrex.mm"
include "cardidm.mm"
include "cardalephex.mm"
include "mpbii.mm"
include "wa.mm"
include "r19.29.mm"
include "biimparc.mm"
include "rexlimivw.mm"
include "syl.mm"
include "ex.mm"
include "syl5.mm"
include "syl5bir.mm"
include "cfn.mm"
include "nnfi.mm"
include "pwfi.mm"
include "sylib.mm"
include "finnum.mm"
include "pm2.61d2.mm"
include "cen.mm"
include "wbr.mm"
include "oncardid.mm"
include "pwen.mm"
include "ennum.mm"
include "3syl.mm"
include "syl5ibcom.mm"
include "ralrimiv.mm"
include "impbii.mm"

theorem dfac12k
  let vx: setvar x
  let vy: setvar y
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vz: setvar z

  disjoint x y
  disjoint a b
  disjoint a f
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b f
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint x z
  disjoint y z
  assert |- ( A. x e. On ~P x e. dom card <-> A. y e. On ~P ( aleph ` y ) e. dom card )

  proof
    vx
    cv
    #
    cpw
    #
    ccrd
    cdm
    #
    wcel
    #
    vx
    con0
    wral
    #
    vy
    cv
    #
    cale
    cfv
    #
    cpw
    #
    @2
    wcel
    #
    vy
    con0
    wral
    #
    @4
    @8
    vy
    con0
    @6
    con0
    wcel
    @4
    @8
    wi
    @5
    alephon
    @3
    @8
    vx
    @6
    con0
    @0
    @6
    wceq
    @1
    @7
    @2
    @0
    @6
    pweq
    eleq1d
    rspcv
    ax-mp
    ralrimivw
    @9
    @3
    vx
    con0
    @9
    @0
    ccrd
    cfv
    #
    cpw
    #
    @2
    wcel
    #
    @0
    con0
    wcel
    #
    @3
    @9
    @10
    com
    wcel
    #
    @12
    @14
    wn
    #
    com
    @10
    wss
    #
    @9
    @12
    com
    con0
    wcel
    @10
    con0
    wcel
    @16
    @15
    wb
    omelon
    @0
    cardon
    com
    @10
    ontri1
    mp2an
    @16
    @10
    @6
    wceq
    #
    vy
    con0
    wrex
    #
    @9
    @12
    @16
    @10
    ccrd
    cfv
    @10
    wceq
    @18
    @0
    cardidm
    vy
    @10
    cardalephex
    mpbii
    @9
    @18
    @12
    @9
    @18
    wa
    @8
    @17
    wa
    #
    vy
    con0
    wrex
    @12
    @8
    @17
    vy
    con0
    r19.29
    @19
    @12
    vy
    con0
    @17
    @12
    @8
    @17
    @11
    @7
    @2
    @10
    @6
    pweq
    eleq1d
    biimparc
    rexlimivw
    syl
    ex
    syl5
    syl5bir
    @14
    @11
    cfn
    wcel
    #
    @12
    @14
    @10
    cfn
    wcel
    @20
    @10
    nnfi
    @10
    pwfi
    sylib
    @11
    finnum
    syl
    pm2.61d2
    @13
    @10
    @0
    cen
    wbr
    @11
    @1
    cen
    wbr
    @12
    @3
    wb
    @0
    oncardid
    @10
    @0
    pwen
    @11
    @1
    ennum
    3syl
    syl5ibcom
    ralrimiv
    impbii
end
