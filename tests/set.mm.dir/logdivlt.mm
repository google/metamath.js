include "cr.mm"
include "wcel.mm"
include "ceu.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "clt.mm"
include "clog.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "wi.mm"
include "w3a.mm"
include "logdivlti.mm"
include "ex.mm"
include "3expa.mm"
include "an32s.mm"
include "adantrr.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "fveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "eqcomd.mm"
include "a1i.mm"
include "ancoms.mm"
include "orim12d.mm"
include "con3d.mm"
include "wb.mm"
include "crp.mm"
include "simpl.mm"
include "cc0.mm"
include "epos.mm"
include "0re.mm"
include "ere.mm"
include "ltletr.mm"
include "mp3an12.mm"
include "mpani.mm"
include "imp.mm"
include "elrpd.mm"
include "relogcl.mm"
include "rerpdivcl.mm"
include "mpancom.mm"
include "syl.mm"
include "axlttri.mm"
include "syl2anr.mm"
include "ad2ant2r.mm"
include "3imtr4d.mm"
include "impbid.mm"

theorem logdivlt
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ _e <_ A ) /\ ( B e. RR /\ _e <_ B ) ) -> ( A < B <-> ( ( log ` B ) / B ) < ( ( log ` A ) / A ) ) )

  proof
    cA
    cr
    wcel
    #
    ceu
    cA
    cle
    wbr
    #
    wa
    #
    cB
    cr
    wcel
    #
    ceu
    cB
    cle
    wbr
    #
    wa
    #
    wa
    #
    cA
    cB
    clt
    wbr
    #
    cB
    clog
    cfv
    #
    cB
    cdiv
    co
    #
    cA
    clog
    cfv
    #
    cA
    cdiv
    co
    #
    clt
    wbr
    #
    @2
    @3
    @7
    @12
    wi
    #
    @4
    @0
    @3
    @1
    @13
    @0
    @3
    @1
    @13
    @0
    @3
    @1
    w3a
    @7
    @12
    cA
    cB
    logdivlti
    ex
    3expa
    an32s
    adantrr
    @6
    @9
    @11
    wceq
    #
    @11
    @9
    clt
    wbr
    #
    wo
    #
    wn
    #
    cA
    cB
    wceq
    #
    cB
    cA
    clt
    wbr
    #
    wo
    #
    wn
    #
    @12
    @7
    @6
    @20
    @16
    @6
    @18
    @14
    @19
    @15
    @18
    @14
    wi
    @6
    @18
    @11
    @9
    @18
    @10
    @8
    cA
    cB
    cdiv
    cA
    cB
    clog
    fveq2
    @18
    id
    oveq12d
    eqcomd
    a1i
    @5
    @2
    @19
    @15
    wi
    #
    @5
    @0
    @22
    @1
    @3
    @0
    @4
    @22
    @3
    @0
    @4
    @22
    @3
    @0
    @4
    w3a
    @19
    @15
    cB
    cA
    logdivlti
    ex
    3expa
    an32s
    adantrr
    ancoms
    orim12d
    con3d
    @5
    @9
    cr
    wcel
    #
    @11
    cr
    wcel
    #
    @12
    @17
    wb
    @2
    @5
    cB
    crp
    wcel
    #
    @23
    @5
    cB
    @3
    @4
    simpl
    @3
    @4
    cc0
    cB
    clt
    wbr
    #
    @3
    cc0
    ceu
    clt
    wbr
    #
    @4
    @26
    epos
    cc0
    cr
    wcel
    #
    ceu
    cr
    wcel
    #
    @3
    @27
    @4
    wa
    @26
    wi
    0re
    ere
    cc0
    ceu
    cB
    ltletr
    mp3an12
    mpani
    imp
    elrpd
    @8
    cr
    wcel
    @25
    @23
    cB
    relogcl
    @8
    cB
    rerpdivcl
    mpancom
    syl
    @2
    cA
    crp
    wcel
    #
    @24
    @2
    cA
    @0
    @1
    simpl
    @0
    @1
    cc0
    cA
    clt
    wbr
    #
    @0
    @27
    @1
    @31
    epos
    @28
    @29
    @0
    @27
    @1
    wa
    @31
    wi
    0re
    ere
    cc0
    ceu
    cA
    ltletr
    mp3an12
    mpani
    imp
    elrpd
    @10
    cr
    wcel
    @30
    @24
    cA
    relogcl
    @10
    cA
    rerpdivcl
    mpancom
    syl
    @9
    @11
    axlttri
    syl2anr
    @0
    @3
    @7
    @21
    wb
    @1
    @4
    cA
    cB
    axlttri
    ad2ant2r
    3imtr4d
    impbid
end
