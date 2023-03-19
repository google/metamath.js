include "ccmn.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "cntzssv.mm"
include "a1i.mm"
include "cv.mm"
include "w3a.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "simpl1.mm"
include "simpl3.mm"
include "simp2.mm"
include "sselda.mm"
include "eqid.mm"
include "cmncom.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "wb.mm"
include "cntzel.mm"
include "3adant1.mm"
include "mpbird.mm"
include "3expia.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem cntzcmn
  let cB: class B
  let cS: class S
  let cG: class G
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  assume cntzcmn.b: |- B = ( Base ` G )
  assume cntzcmn.z: |- Z = ( Cntz ` G )


  assert |- ( ( G e. CMnd /\ S C_ B ) -> ( Z ` S ) = B )

  proof
    cG
    ccmn
    wcel
    #
    cS
    cB
    wss
    #
    wa
    #
    cS
    cZ
    cfv
    #
    cB
    @3
    cB
    wss
    @2
    cB
    cS
    cG
    cZ
    cntzcmn.b
    cntzcmn.z
    cntzssv
    a1i
    @2
    vx
    cB
    @3
    @0
    @1
    vx
    cv
    #
    cB
    wcel
    #
    @4
    @3
    wcel
    #
    @0
    @1
    @5
    w3a
    #
    @6
    @4
    vy
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    @8
    @4
    @9
    co
    wceq
    #
    vy
    cS
    wral
    #
    @7
    @10
    vy
    cS
    @7
    @8
    cS
    wcel
    #
    wa
    @0
    @5
    @8
    cB
    wcel
    @10
    @0
    @1
    @5
    @12
    simpl1
    @0
    @1
    @5
    @12
    simpl3
    @7
    cS
    cB
    @8
    @0
    @1
    @5
    simp2
    sselda
    cB
    @9
    cG
    @4
    @8
    cntzcmn.b
    @9
    eqid
    #
    cmncom
    syl3anc
    ralrimiva
    @1
    @5
    @6
    @11
    wb
    @0
    vy
    cB
    @9
    cS
    cG
    @4
    cZ
    cntzcmn.b
    @13
    cntzcmn.z
    cntzel
    3adant1
    mpbird
    3expia
    ssrdv
    eqssd
end
