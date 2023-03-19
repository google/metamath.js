include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cv.mm"
include "cplusg.mm"
include "wceq.mm"
include "wrex.mm"
include "cmpt2.mm"
include "crn.mm"
include "cbs.mm"
include "eqid.mm"
include "lsmval.mm"
include "3adant3.mm"
include "rexeqdv.mm"
include "cvv.mm"
include "wral.mm"
include "wb.mm"
include "ovex.mm"
include "rgen2w.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "rexrnmpt2.mm"
include "ax-mp.mm"
include "syl6bb.mm"
include "wa.mm"
include "3adant1.mm"
include "oveq2.mm"
include "adantr.mm"
include "cgrp.mm"
include "subgrcl.mm"
include "3ad2ant1.mm"
include "ad2antrr.mm"
include "wss.mm"
include "subgss.mm"
include "simplr.mm"
include "sseldd.mm"
include "3ad2ant2.mm"
include "simprl.mm"
include "3ad2ant3.mm"
include "simprr.mm"
include "grpass.mm"
include "syl13anc.mm"
include "2rexbidva.mm"
include "bitr4d.mm"
include "rexbidva.mm"
include "cmnd.mm"
include "grpmnd.mm"
include "syl.mm"
include "lsmssv.mm"
include "syl3anc.mm"
include "lsmelvalx.mm"
include "3bitr4d.mm"
include "eqrdv.mm"

theorem lsmass
  let c.po: class .(+)
  let cR: class R
  let cT: class T
  let cU: class U
  let cG: class G
  let va: setvar a
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vb: setvar b
  assume lsmub1.p: |- .(+) = ( LSSum ` G )


  assert |- ( ( R e. ( SubGrp ` G ) /\ T e. ( SubGrp ` G ) /\ U e. ( SubGrp ` G ) ) -> ( ( R .(+) T ) .(+) U ) = ( R .(+) ( T .(+) U ) ) )

  proof
    cR
    cG
    csubg
    cfv
    #
    wcel
    #
    cT
    @0
    wcel
    #
    cU
    @0
    wcel
    #
    w3a
    #
    vx
    cR
    cT
    c.po
    co
    #
    cU
    c.po
    co
    #
    cR
    cT
    cU
    c.po
    co
    #
    c.po
    co
    #
    @4
    vx
    cv
    #
    vy
    cv
    #
    vc
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vc
    cU
    wrex
    #
    vy
    @5
    wrex
    #
    @9
    va
    cv
    #
    vz
    cv
    #
    @12
    co
    #
    wceq
    #
    vz
    @7
    wrex
    #
    va
    cR
    wrex
    #
    @9
    @6
    wcel
    #
    @9
    @8
    wcel
    #
    @4
    @16
    @9
    @17
    vb
    cv
    #
    @12
    co
    #
    @11
    @12
    co
    #
    wceq
    #
    vc
    cU
    wrex
    #
    vb
    cT
    wrex
    #
    va
    cR
    wrex
    #
    @22
    @4
    @16
    @15
    vy
    va
    vb
    cR
    cT
    @26
    cmpt2
    #
    crn
    #
    wrex
    #
    @31
    @4
    @15
    vy
    @5
    @33
    @1
    @2
    @5
    @33
    wceq
    @3
    va
    vb
    cG
    cbs
    cfv
    #
    @12
    c.po
    cR
    cT
    cG
    @35
    eqid
    #
    @12
    eqid
    #
    lsmub1.p
    lsmval
    3adant3
    rexeqdv
    @26
    cvv
    wcel
    #
    vb
    cT
    wral
    va
    cR
    wral
    @34
    @31
    wb
    @38
    va
    vb
    cR
    cT
    @17
    @25
    @12
    ovex
    rgen2w
    @15
    @29
    va
    vb
    vy
    cR
    cT
    @26
    @32
    cvv
    @32
    eqid
    @10
    @26
    wceq
    #
    @14
    @28
    vc
    cU
    @39
    @13
    @27
    @9
    @10
    @26
    @11
    @12
    oveq1
    eqeq2d
    rexbidv
    rexrnmpt2
    ax-mp
    syl6bb
    @4
    @21
    @30
    va
    cR
    @4
    @17
    cR
    wcel
    #
    wa
    #
    @21
    @9
    @17
    @25
    @11
    @12
    co
    #
    @12
    co
    #
    wceq
    #
    vc
    cU
    wrex
    vb
    cT
    wrex
    #
    @30
    @4
    @21
    @45
    wb
    @40
    @4
    @21
    @20
    vz
    vb
    vc
    cT
    cU
    @42
    cmpt2
    #
    crn
    #
    wrex
    #
    @45
    @4
    @20
    vz
    @7
    @47
    @2
    @3
    @7
    @47
    wceq
    @1
    vb
    vc
    @35
    @12
    c.po
    cT
    cU
    cG
    @36
    @37
    lsmub1.p
    lsmval
    3adant1
    rexeqdv
    @42
    cvv
    wcel
    #
    vc
    cU
    wral
    vb
    cT
    wral
    @48
    @45
    wb
    @49
    vb
    vc
    cT
    cU
    @25
    @11
    @12
    ovex
    rgen2w
    @20
    @44
    vb
    vc
    vz
    cT
    cU
    @42
    @46
    cvv
    @46
    eqid
    @18
    @42
    wceq
    @19
    @43
    @9
    @18
    @42
    @17
    @12
    oveq2
    eqeq2d
    rexrnmpt2
    ax-mp
    syl6bb
    adantr
    @41
    @28
    @44
    vb
    vc
    cT
    cU
    @41
    @25
    cT
    wcel
    #
    @11
    cU
    wcel
    #
    wa
    #
    wa
    #
    @27
    @43
    @9
    @53
    cG
    cgrp
    wcel
    #
    @17
    @35
    wcel
    @25
    @35
    wcel
    @11
    @35
    wcel
    @27
    @43
    wceq
    @4
    @54
    @40
    @52
    @1
    @2
    @54
    @3
    cR
    cG
    subgrcl
    3ad2ant1
    #
    ad2antrr
    @53
    cR
    @35
    @17
    @4
    cR
    @35
    wss
    #
    @40
    @52
    @1
    @2
    @56
    @3
    @35
    cR
    cG
    @36
    subgss
    3ad2ant1
    #
    ad2antrr
    @4
    @40
    @52
    simplr
    sseldd
    @53
    cT
    @35
    @25
    @4
    cT
    @35
    wss
    #
    @40
    @52
    @2
    @1
    @58
    @3
    @35
    cT
    cG
    @36
    subgss
    3ad2ant2
    #
    ad2antrr
    @41
    @50
    @51
    simprl
    sseldd
    @53
    cU
    @35
    @11
    @4
    cU
    @35
    wss
    #
    @40
    @52
    @3
    @1
    @60
    @2
    @35
    cU
    cG
    @36
    subgss
    3ad2ant3
    #
    ad2antrr
    @41
    @50
    @51
    simprr
    sseldd
    @35
    @12
    cG
    @17
    @25
    @11
    @36
    @37
    grpass
    syl13anc
    eqeq2d
    2rexbidva
    bitr4d
    rexbidva
    bitr4d
    @4
    @54
    @5
    @35
    wss
    #
    @60
    @23
    @16
    wb
    @55
    @4
    cG
    cmnd
    wcel
    #
    @56
    @58
    @62
    @4
    @54
    @63
    @55
    cG
    grpmnd
    syl
    #
    @57
    @59
    @35
    c.po
    cR
    cT
    cG
    @36
    lsmub1.p
    lsmssv
    syl3anc
    @61
    vy
    vc
    @35
    @12
    c.po
    @5
    cU
    cG
    cgrp
    @9
    @36
    @37
    lsmub1.p
    lsmelvalx
    syl3anc
    @4
    @54
    @56
    @7
    @35
    wss
    #
    @24
    @22
    wb
    @55
    @57
    @4
    @63
    @58
    @60
    @65
    @64
    @59
    @61
    @35
    c.po
    cT
    cU
    cG
    @36
    lsmub1.p
    lsmssv
    syl3anc
    va
    vz
    @35
    @12
    c.po
    cR
    @7
    cG
    cgrp
    @9
    @36
    @37
    lsmub1.p
    lsmelvalx
    syl3anc
    3bitr4d
    eqrdv
end
