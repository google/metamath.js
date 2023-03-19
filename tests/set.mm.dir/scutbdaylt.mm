include "csur.mm"
include "wcel.mm"
include "csn.mm"
include "csslt.mm"
include "wbr.mm"
include "wa.mm"
include "cscut.mm"
include "co.mm"
include "wne.mm"
include "w3a.mm"
include "cbday.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "crab.mm"
include "cima.mm"
include "cint.mm"
include "wceq.mm"
include "c0.mm"
include "simp2l.mm"
include "simp2r.mm"
include "snnzg.mm"
include "3ad2ant1.mm"
include "sslttr.mm"
include "syl3anc.mm"
include "scutbday.mm"
include "syl.mm"
include "wfn.mm"
include "bdayfn.mm"
include "ssrab2.mm"
include "simp1.mm"
include "simp2.mm"
include "sneq.mm"
include "breq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "fnfvima.mm"
include "mp3an12i.mm"
include "intss1.mm"
include "eqsstrd.mm"
include "crio.mm"
include "simprl.mm"
include "simprr.mm"
include "adantr.mm"
include "eqeq1d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "biimpa.mm"
include "wreu.mm"
include "wb.mm"
include "biimpri.mm"
include "conway.mm"
include "fveq2.mm"
include "riota2.mm"
include "syl2an2r.mm"
include "mpbid.mm"
include "scutval.mm"
include "eqtr4d.mm"
include "ex.mm"
include "necon3d.mm"
include "3impia.mm"
include "con0.mm"
include "bdayelon.mm"
include "onelpss.mm"
include "mp2an.mm"

theorem scutbdaylt
  let cA: class A
  let cB: class B
  let cX: class X
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( X e. No /\ ( A <<s { X } /\ { X } <<s B ) /\ X =/= ( A |s B ) ) -> ( bday ` ( A |s B ) ) e. ( bday ` X ) )

  proof
    cX
    csur
    wcel
    #
    cA
    cX
    csn
    #
    csslt
    wbr
    #
    @1
    cB
    csslt
    wbr
    #
    wa
    #
    cX
    cA
    cB
    cscut
    co
    #
    wne
    #
    w3a
    #
    @5
    cbday
    cfv
    #
    cX
    cbday
    cfv
    #
    wss
    #
    @8
    @9
    wne
    #
    @8
    @9
    wcel
    #
    @7
    @8
    cbday
    cA
    vy
    cv
    #
    csn
    #
    csslt
    wbr
    #
    @14
    cB
    csslt
    wbr
    #
    wa
    #
    vy
    csur
    crab
    #
    cima
    #
    cint
    #
    @9
    @7
    cA
    cB
    csslt
    wbr
    #
    @8
    @20
    wceq
    #
    @7
    @2
    @3
    @1
    c0
    wne
    #
    @21
    @0
    @2
    @3
    @6
    simp2l
    @0
    @2
    @3
    @6
    simp2r
    @0
    @4
    @23
    @6
    cX
    csur
    snnzg
    #
    3ad2ant1
    cA
    @1
    cB
    sslttr
    #
    syl3anc
    vy
    cA
    cB
    scutbday
    #
    syl
    @7
    @9
    @19
    wcel
    #
    @20
    @9
    wss
    cbday
    csur
    wfn
    @18
    csur
    wss
    @7
    cX
    @18
    wcel
    #
    @27
    bdayfn
    @17
    vy
    csur
    ssrab2
    @7
    @0
    @4
    @28
    @0
    @4
    @6
    simp1
    @0
    @4
    @6
    simp2
    @17
    @4
    vy
    cX
    csur
    @13
    cX
    wceq
    #
    @15
    @2
    @16
    @3
    @29
    @14
    @1
    cA
    csslt
    @13
    cX
    sneq
    #
    breq2d
    @29
    @14
    @1
    cB
    csslt
    @30
    breq1d
    anbi12d
    elrab
    #
    sylanbrc
    csur
    @18
    cbday
    cX
    fnfvima
    mp3an12i
    @9
    @19
    intss1
    syl
    eqsstrd
    @0
    @4
    @6
    @11
    @0
    @4
    wa
    #
    @8
    @9
    cX
    @5
    @32
    @8
    @9
    wceq
    #
    cX
    @5
    wceq
    @32
    @33
    wa
    #
    cX
    vx
    cv
    #
    cbday
    cfv
    #
    @20
    wceq
    #
    vx
    @18
    crio
    #
    @5
    @34
    @9
    @20
    wceq
    #
    cX
    @38
    wceq
    #
    @32
    @33
    @39
    @32
    @33
    @20
    @9
    wceq
    @39
    @32
    @8
    @20
    @9
    @32
    @21
    @22
    @32
    @2
    @3
    @23
    @21
    @0
    @2
    @3
    simprl
    @0
    @2
    @3
    simprr
    @0
    @23
    @4
    @24
    adantr
    @25
    syl3anc
    #
    @26
    syl
    eqeq1d
    @20
    @9
    eqcom
    syl6bb
    biimpa
    @32
    @28
    @33
    @37
    vx
    @18
    wreu
    #
    @39
    @40
    wb
    @28
    @32
    @31
    biimpri
    @34
    @21
    @42
    @32
    @21
    @33
    @41
    adantr
    #
    vx
    vy
    cA
    cB
    conway
    syl
    @28
    @42
    wa
    @39
    @38
    cX
    wceq
    @40
    @37
    @39
    vx
    @18
    cX
    @35
    cX
    wceq
    @36
    @9
    @20
    @35
    cX
    cbday
    fveq2
    eqeq1d
    riota2
    @38
    cX
    eqcom
    syl6bb
    syl2an2r
    mpbid
    @34
    @21
    @5
    @38
    wceq
    @43
    vx
    vy
    cA
    cB
    scutval
    syl
    eqtr4d
    ex
    necon3d
    3impia
    @8
    con0
    wcel
    @9
    con0
    wcel
    @12
    @10
    @11
    wa
    wb
    @5
    bdayelon
    cX
    bdayelon
    @8
    @9
    onelpss
    mp2an
    sylanbrc
end
