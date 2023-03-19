include "wcel.mm"
include "ciun.mm"
include "cixp.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt2.mm"
include "cvv.mm"
include "cxp.mm"
include "wfo.mm"
include "cwdom.mm"
include "wbr.mm"
include "wf.mm"
include "wral.mm"
include "wfn.mm"
include "vex.mm"
include "elixp.mm"
include "simprbi.mm"
include "ssiun2.mm"
include "sseld.mm"
include "ralimia.mm"
include "syl.mm"
include "nfv.mm"
include "nfiu1.mm"
include "nfel2.mm"
include "weq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "cbvral.mm"
include "sylib.mm"
include "adantl.mm"
include "ralrimiva.mm"
include "eqid.mm"
include "fmpt2.mm"
include "cmap.mm"
include "co.mm"
include "wss.mm"
include "ixpssmap2g.mm"
include "3ad2ant2.mm"
include "ovex.mm"
include "ssex.mm"
include "simp1.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "simp2.mm"
include "fex2.mm"
include "syl3anc.mm"
include "crn.mm"
include "ffn.mm"
include "dffn4.mm"
include "wceq.mm"
include "wb.mm"
include "wrex.mm"
include "cab.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "n0.mm"
include "eliun.mm"
include "nfixp1.mm"
include "nfrex.mm"
include "wa.mm"
include "cif.mm"
include "cmpt.mm"
include "csb.mm"
include "simplrr.mm"
include "iftrue.mm"
include "csbeq1a.mm"
include "equcoms.mm"
include "eqcomd.mm"
include "eleq12d.mm"
include "syl5ibrcom.mm"
include "wn.mm"
include "adantr.mm"
include "nfcsb1v.mm"
include "r19.21bi.mm"
include "iffalse.mm"
include "pm2.61d.mm"
include "cdm.mm"
include "ixpfn.mm"
include "fndm.mm"
include "dmex.mm"
include "syl6eqelr.mm"
include "mptelixpg.mm"
include "mpbird.mm"
include "nfcv.mm"
include "cbvixp.mm"
include "syl6eleqr.mm"
include "simprl.mm"
include "fvmpt.mm"
include "ad2antrl.mm"
include "fveq1.mm"
include "eqeq2d.mm"
include "rspc2ev.mm"
include "exp32.mm"
include "rexlimd.mm"
include "syl5bi.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "3ad2ant3.mm"
include "alrimiv.mm"
include "ssab.mm"
include "sylibr.mm"
include "rnmpt2.mm"
include "syl6sseqr.mm"
include "frn.mm"
include "eqssd.mm"
include "foeq3.mm"
include "fowdom.mm"

theorem ixpiunwdom
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint f g
  disjoint f k
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g k
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B f
  disjoint B g
  disjoint B k
  disjoint B y
  disjoint B z
  disjoint V f
  disjoint V z
  disjoint W f
  disjoint W z
  assert |- ( ( A e. V /\ U_ x e. A B e. W /\ X_ x e. A B =/= (/) ) -> U_ x e. A B ~<_* ( X_ x e. A B X. A ) )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    cB
    ciun
    #
    cW
    wcel
    #
    vx
    cA
    cB
    cixp
    #
    c0
    wne
    #
    w3a
    #
    vf
    vy
    @3
    cA
    vy
    cv
    #
    vf
    cv
    #
    cfv
    #
    cmpt2
    #
    cvv
    wcel
    #
    @3
    cA
    cxp
    #
    @1
    @9
    wfo
    #
    @1
    @11
    cwdom
    wbr
    @5
    @11
    @1
    @9
    wf
    #
    @11
    cvv
    wcel
    #
    @2
    @10
    @5
    @8
    @1
    wcel
    #
    vy
    cA
    wral
    #
    vf
    @3
    wral
    @13
    @5
    @16
    vf
    @3
    @7
    @3
    wcel
    #
    @16
    @5
    @17
    vx
    cv
    #
    @7
    cfv
    #
    @1
    wcel
    #
    vx
    cA
    wral
    #
    @16
    @17
    @19
    cB
    wcel
    #
    vx
    cA
    wral
    #
    @21
    @17
    @7
    cA
    wfn
    @23
    vx
    cA
    cB
    @7
    vf
    vex
    elixp
    simprbi
    @22
    @20
    vx
    cA
    @18
    cA
    wcel
    #
    cB
    @1
    @19
    vx
    cA
    cB
    ssiun2
    sseld
    ralimia
    syl
    @20
    @15
    vx
    vy
    cA
    @20
    vy
    nfv
    vx
    @8
    @1
    vx
    cA
    cB
    nfiu1
    nfel2
    vx
    vy
    weq
    @19
    @8
    @1
    @18
    @6
    @7
    fveq2
    eleq1d
    cbvral
    sylib
    adantl
    ralrimiva
    vf
    vy
    @3
    cA
    @8
    @1
    @9
    @9
    eqid
    #
    fmpt2
    sylib
    #
    @5
    @3
    cvv
    wcel
    #
    @0
    @14
    @5
    @3
    @1
    cA
    cmap
    co
    #
    wss
    #
    @27
    @2
    @0
    @29
    @4
    vx
    cA
    cB
    cW
    ixpssmap2g
    3ad2ant2
    @3
    @28
    @1
    cA
    cmap
    ovex
    ssex
    syl
    @0
    @2
    @4
    simp1
    @3
    cA
    cvv
    cV
    xpexg
    syl2anc
    @0
    @2
    @4
    simp2
    @11
    @1
    @9
    cvv
    cW
    fex2
    syl3anc
    @5
    @12
    @11
    @9
    crn
    #
    @9
    wfo
    #
    @5
    @9
    @11
    wfn
    #
    @31
    @5
    @13
    @32
    @26
    @11
    @1
    @9
    ffn
    syl
    @11
    @9
    dffn4
    sylib
    @5
    @1
    @30
    wceq
    @12
    @31
    wb
    @5
    @1
    @30
    @5
    @1
    vz
    cv
    #
    @8
    wceq
    #
    vy
    cA
    wrex
    #
    vf
    @3
    wrex
    #
    vz
    cab
    #
    @30
    @5
    @33
    @1
    wcel
    #
    @36
    wi
    #
    vz
    wal
    @1
    @37
    wss
    @5
    @39
    vz
    @4
    @0
    @39
    @2
    @4
    vg
    cv
    #
    @3
    wcel
    #
    vg
    wex
    @39
    vg
    @3
    n0
    @41
    @39
    vg
    @38
    @33
    cB
    wcel
    #
    vx
    cA
    wrex
    @41
    @36
    vx
    @33
    cA
    cB
    eliun
    @41
    @42
    @36
    vx
    cA
    vx
    @40
    @3
    vx
    cA
    cB
    nfixp1
    #
    nfel2
    @35
    vx
    vf
    @3
    @43
    @35
    vx
    nfv
    nfrex
    @41
    @24
    @42
    @36
    @41
    @24
    @42
    wa
    #
    wa
    #
    vk
    cA
    vk
    vx
    weq
    #
    @33
    vk
    cv
    #
    @40
    cfv
    #
    cif
    #
    cmpt
    #
    @3
    wcel
    @24
    @33
    @18
    @50
    cfv
    #
    wceq
    #
    @36
    @45
    @50
    vk
    cA
    vx
    @47
    cB
    csb
    #
    cixp
    #
    @3
    @45
    @50
    @54
    wcel
    #
    @49
    @53
    wcel
    #
    vk
    cA
    wral
    #
    @45
    @56
    vk
    cA
    @45
    @47
    cA
    wcel
    #
    wa
    #
    @46
    @56
    @59
    @56
    @46
    @42
    @41
    @24
    @42
    @58
    simplrr
    @46
    @49
    @33
    @53
    cB
    @46
    @33
    @48
    iftrue
    #
    @46
    cB
    @53
    cB
    @53
    wceq
    vx
    vk
    vx
    @47
    cB
    csbeq1a
    #
    equcoms
    eqcomd
    eleq12d
    syl5ibrcom
    @59
    @56
    @46
    wn
    #
    @48
    @53
    wcel
    #
    @45
    @63
    vk
    cA
    @45
    @18
    @40
    cfv
    #
    cB
    wcel
    #
    vx
    cA
    wral
    #
    @63
    vk
    cA
    wral
    @41
    @66
    @44
    @41
    @40
    cA
    wfn
    #
    @66
    vx
    cA
    cB
    @40
    vg
    vex
    #
    elixp
    simprbi
    adantr
    @65
    @63
    vx
    vk
    cA
    @65
    vk
    nfv
    vx
    @48
    @53
    vx
    @47
    cB
    nfcsb1v
    #
    nfel2
    vx
    vk
    weq
    @64
    @48
    cB
    @53
    @18
    @47
    @40
    fveq2
    @61
    eleq12d
    cbvral
    sylib
    r19.21bi
    @62
    @49
    @48
    @53
    @46
    @33
    @48
    iffalse
    eleq1d
    syl5ibrcom
    pm2.61d
    ralrimiva
    @45
    cA
    cvv
    wcel
    @55
    @57
    wb
    @45
    cA
    @40
    cdm
    #
    cvv
    @45
    @67
    @70
    cA
    wceq
    @41
    @67
    @44
    vx
    cA
    cB
    @40
    ixpfn
    adantr
    cA
    @40
    fndm
    syl
    @40
    @68
    dmex
    syl6eqelr
    vk
    cA
    @49
    @53
    cvv
    mptelixpg
    syl
    mpbird
    vx
    vk
    cA
    cB
    @53
    vk
    cB
    nfcv
    @69
    @61
    cbvixp
    syl6eleqr
    @41
    @24
    @42
    simprl
    @45
    @51
    @33
    @24
    @51
    @33
    wceq
    @41
    @42
    vk
    @18
    @49
    @33
    cA
    @50
    @60
    @50
    eqid
    vz
    vex
    fvmpt
    ad2antrl
    eqcomd
    @34
    @52
    @33
    @6
    @50
    cfv
    #
    wceq
    vf
    vy
    @50
    @18
    @3
    cA
    @7
    @50
    wceq
    @8
    @71
    @33
    @6
    @7
    @50
    fveq1
    eqeq2d
    vy
    vx
    weq
    @71
    @51
    @33
    @6
    @18
    @50
    fveq2
    eqeq2d
    rspc2ev
    syl3anc
    exp32
    rexlimd
    syl5bi
    exlimiv
    sylbi
    3ad2ant3
    alrimiv
    @36
    vz
    @1
    ssab
    sylibr
    vf
    vy
    vz
    @3
    cA
    @8
    @9
    @25
    rnmpt2
    syl6sseqr
    @5
    @13
    @30
    @1
    wss
    @26
    @11
    @1
    @9
    frn
    syl
    eqssd
    @1
    @30
    @11
    @9
    foeq3
    syl
    mpbird
    @9
    cvv
    @1
    @11
    fowdom
    syl2anc
end
