include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "cs4.mm"
include "wceq.mm"
include "cdm.mm"
include "cpr.mm"
include "cun.mm"
include "wf1o.mm"
include "cc0.mm"
include "c1.mm"
include "c2.mm"
include "c3.mm"
include "cop.mm"
include "f1oun2prg.mm"
include "imp.mm"
include "adantr.mm"
include "s4prop.mm"
include "eqeq2d.mm"
include "biimpa.mm"
include "eqcomd.mm"
include "eqidd.mm"
include "f1oeq123d.mm"
include "mpbid.mm"
include "wf1.mm"
include "crn.mm"
include "wf.mm"
include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "wal.mm"
include "dff1o5.mm"
include "dff12.mm"
include "bicomi.mm"
include "anbi1i.mm"
include "sylbb2.mm"
include "wss.mm"
include "ffdm.mm"
include "simpld.mm"
include "anim1i.mm"
include "syl.mm"
include "sylibr.mm"
include "exp31.mm"

theorem s4f1o
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cE: class E
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( A e. S /\ B e. S ) /\ ( C e. S /\ D e. S ) ) -> ( ( ( A =/= B /\ A =/= C /\ A =/= D ) /\ ( B =/= C /\ B =/= D /\ C =/= D ) ) -> ( E = <" A B C D "> -> E : dom E -1-1-onto-> ( { A , B } u. { C , D } ) ) ) )

  proof
    cA
    cS
    wcel
    cB
    cS
    wcel
    wa
    cC
    cS
    wcel
    cD
    cS
    wcel
    wa
    wa
    #
    cA
    cB
    wne
    cA
    cC
    wne
    cA
    cD
    wne
    w3a
    cB
    cC
    wne
    cB
    cD
    wne
    cC
    cD
    wne
    w3a
    wa
    #
    cE
    cA
    cB
    cC
    cD
    cs4
    #
    wceq
    #
    cE
    cdm
    #
    cA
    cB
    cpr
    cC
    cD
    cpr
    cun
    #
    cE
    wf1o
    #
    @0
    @1
    wa
    #
    @3
    wa
    #
    cc0
    c1
    cpr
    c2
    c3
    cpr
    cun
    #
    @5
    cE
    wf1o
    #
    @6
    @8
    @9
    @5
    cc0
    cA
    cop
    c1
    cB
    cop
    cpr
    c2
    cC
    cop
    c3
    cD
    cop
    cpr
    cun
    #
    wf1o
    #
    @10
    @7
    @12
    @3
    @0
    @1
    @12
    cA
    cB
    cC
    cD
    cS
    cS
    cS
    cS
    f1oun2prg
    imp
    adantr
    @8
    @9
    @9
    @5
    @5
    @11
    cE
    @8
    cE
    @11
    @7
    @3
    cE
    @11
    wceq
    @7
    @2
    @11
    cE
    @0
    @2
    @11
    wceq
    @1
    cA
    cB
    cC
    cD
    cS
    s4prop
    adantr
    eqeq2d
    biimpa
    eqcomd
    @8
    @9
    eqidd
    @8
    @5
    eqidd
    f1oeq123d
    mpbid
    @10
    @4
    @5
    cE
    wf1
    #
    cE
    crn
    @5
    wceq
    #
    wa
    #
    @6
    @10
    @4
    @5
    cE
    wf
    #
    vx
    cv
    vy
    cv
    cE
    wbr
    vx
    wmo
    vy
    wal
    #
    wa
    #
    @14
    wa
    #
    @15
    @10
    @9
    @5
    cE
    wf
    #
    @17
    wa
    #
    @14
    wa
    #
    @19
    @10
    @9
    @5
    cE
    wf1
    #
    @14
    wa
    @22
    @9
    @5
    cE
    dff1o5
    @21
    @23
    @14
    @23
    @21
    vx
    vy
    @9
    @5
    cE
    dff12
    bicomi
    anbi1i
    sylbb2
    @21
    @18
    @14
    @20
    @16
    @17
    @20
    @16
    @4
    @9
    wss
    @9
    @5
    cE
    ffdm
    simpld
    anim1i
    anim1i
    syl
    @13
    @18
    @14
    vx
    vy
    @4
    @5
    cE
    dff12
    anbi1i
    sylibr
    @4
    @5
    cE
    dff1o5
    sylibr
    syl
    exp31
end
