include "cusgr.mm"
include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cpr.mm"
include "cedg.mm"
include "wss.mm"
include "wreu.mm"
include "cdif.mm"
include "wral.mm"
include "cfrgr.mm"
include "simpl.mm"
include "cvv.mm"
include "c0.mm"
include "ral0.mm"
include "sneq.mm"
include "difeq2d.mm"
include "difid.mm"
include "syl6eq.mm"
include "preq2.mm"
include "preq1d.mm"
include "sseq1d.mm"
include "reubidv.mm"
include "raleqbidv.mm"
include "ralsng.mm"
include "mpbiri.mm"
include "wn.mm"
include "snprc.mm"
include "rzal.mm"
include "sylbi.mm"
include "pm2.61i.mm"
include "wb.mm"
include "id.mm"
include "difeq1.mm"
include "reueq1.mm"
include "adantl.mm"
include "eqid.mm"
include "frgrusgrfrcond.mm"
include "sylanbrc.mm"

theorem frgr1v
  let cG: class G
  let cN: class N
  let vk: setvar k
  let vl: setvar l
  let vx: setvar x


  assert |- ( ( G e. USGraph /\ ( Vtx ` G ) = { N } ) -> G e. FriendGraph )

  proof
    cG
    cusgr
    wcel
    #
    cG
    cvtx
    cfv
    #
    cN
    csn
    #
    wceq
    #
    wa
    #
    @0
    vx
    cv
    #
    vk
    cv
    #
    cpr
    #
    @5
    vl
    cv
    cpr
    #
    cpr
    #
    cG
    cedg
    cfv
    #
    wss
    #
    vx
    @1
    wreu
    #
    vl
    @1
    @6
    csn
    #
    cdif
    #
    wral
    #
    vk
    @1
    wral
    #
    cG
    cfrgr
    wcel
    @0
    @3
    simpl
    @4
    @16
    @11
    vx
    @2
    wreu
    #
    vl
    @2
    @13
    cdif
    #
    wral
    #
    vk
    @2
    wral
    #
    cN
    cvv
    wcel
    #
    @20
    @21
    @20
    @5
    cN
    cpr
    #
    @8
    cpr
    #
    @10
    wss
    #
    vx
    @2
    wreu
    #
    vl
    c0
    wral
    #
    @25
    vl
    ral0
    @19
    @26
    vk
    cN
    cvv
    @6
    cN
    wceq
    #
    @17
    @25
    vl
    @18
    c0
    @27
    @18
    @2
    @2
    cdif
    c0
    @27
    @13
    @2
    @2
    @6
    cN
    sneq
    difeq2d
    @2
    difid
    syl6eq
    @27
    @11
    @24
    vx
    @2
    @27
    @9
    @23
    @10
    @27
    @7
    @22
    @8
    @6
    cN
    @5
    preq2
    preq1d
    sseq1d
    reubidv
    raleqbidv
    ralsng
    mpbiri
    @21
    wn
    @2
    c0
    wceq
    @20
    cN
    snprc
    @19
    vk
    @2
    rzal
    sylbi
    pm2.61i
    @3
    @16
    @20
    wb
    @0
    @3
    @15
    @19
    vk
    @1
    @2
    @3
    id
    @3
    @12
    @17
    vl
    @14
    @18
    @1
    @2
    @13
    difeq1
    @11
    vx
    @1
    @2
    reueq1
    raleqbidv
    raleqbidv
    adantl
    mpbiri
    vx
    vk
    @10
    cG
    @1
    vl
    @1
    eqid
    @10
    eqid
    frgrusgrfrcond
    sylanbrc
end
