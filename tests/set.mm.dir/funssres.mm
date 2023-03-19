include "wfun.mm"
include "wss.mm"
include "wa.mm"
include "cdm.mm"
include "cres.mm"
include "wceq.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "wi.mm"
include "ssel.mm"
include "vex.mm"
include "opeldm.mm"
include "a1i.mm"
include "jcad.mm"
include "adantl.mm"
include "weu.mm"
include "wex.mm"
include "funeu2.mm"
include "eldm2.mm"
include "ancrd.mm"
include "eximdv.mm"
include "syl5bi.mm"
include "imp.mm"
include "eupick.mm"
include "syl2an.mm"
include "exp43.mm"
include "com23.mm"
include "com34.mm"
include "pm2.43d.mm"
include "impd.mm"
include "impbid.mm"
include "opelres.mm"
include "syl6rbbr.mm"
include "alrimivv.mm"
include "wrel.mm"
include "relres.mm"
include "funrel.mm"
include "relss.mm"
include "mpan9.mm"
include "eqrel.mm"
include "sylancr.mm"
include "mpbird.mm"

theorem funssres
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( Fun F /\ G C_ F ) -> ( F |` dom G ) = G )

  proof
    cF
    wfun
    #
    cG
    cF
    wss
    #
    wa
    #
    cF
    cG
    cdm
    #
    cres
    #
    cG
    wceq
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    @4
    wcel
    #
    @8
    cG
    wcel
    #
    wb
    #
    vy
    wal
    vx
    wal
    #
    @2
    @11
    vx
    vy
    @2
    @10
    @8
    cF
    wcel
    #
    @6
    @3
    wcel
    #
    wa
    #
    @9
    @2
    @10
    @15
    @1
    @10
    @15
    wi
    @0
    @1
    @10
    @13
    @14
    cG
    cF
    @8
    ssel
    #
    @10
    @14
    wi
    @1
    @6
    @7
    cG
    vx
    vex
    #
    vy
    vex
    #
    opeldm
    a1i
    jcad
    adantl
    @2
    @13
    @14
    @10
    @2
    @13
    @14
    @10
    wi
    @2
    @13
    @14
    @13
    @10
    @0
    @1
    @13
    @14
    @13
    @10
    wi
    #
    wi
    #
    wi
    @0
    @13
    @1
    @20
    @0
    @13
    @1
    @14
    @19
    @0
    @13
    wa
    @13
    vy
    weu
    @13
    @10
    wa
    #
    vy
    wex
    #
    @19
    @1
    @14
    wa
    vy
    @6
    @7
    cF
    funeu2
    @1
    @14
    @22
    @14
    @10
    vy
    wex
    @1
    @22
    vy
    @6
    cG
    @17
    eldm2
    @1
    @10
    @21
    vy
    @1
    @10
    @13
    @16
    ancrd
    eximdv
    syl5bi
    imp
    @13
    @10
    vy
    eupick
    syl2an
    exp43
    com23
    imp
    com34
    pm2.43d
    impd
    impbid
    @6
    @7
    cF
    @3
    @18
    opelres
    syl6rbbr
    alrimivv
    @2
    @4
    wrel
    cG
    wrel
    #
    @5
    @12
    wb
    cF
    @3
    relres
    @0
    cF
    wrel
    @1
    @23
    cF
    funrel
    cG
    cF
    relss
    mpan9
    vx
    vy
    @4
    cG
    eqrel
    sylancr
    mpbird
end
