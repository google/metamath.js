include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "crab.mm"
include "crio.mm"
include "cgrp.mm"
include "cbs.mm"
include "wss.mm"
include "w3a.mm"
include "csubg.mm"
include "subgrcl.mm"
include "syl.mm"
include "eqid.mm"
include "subgss.mm"
include "3jca.mm"
include "pj1val.mm"
include "sylan.mm"
include "wreu.mm"
include "pj1eu.mm"
include "riotacl2.mm"
include "eqeltrd.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "elrab.mm"
include "simprbi.mm"
include "simprr.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "lsmcom2.mm"
include "syl3anc.mm"
include "eleqtrd.mm"
include "syl31anc.mm"
include "wf.mm"
include "pj1f.mm"
include "ffvelrnd.mm"
include "sseldd.mm"
include "simprl.mm"
include "cntzi.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "oveq2.mm"
include "rspcev.mm"
include "wb.mm"
include "simpll.mm"
include "cin.mm"
include "csn.mm"
include "incom.mm"
include "syl5eq.mm"
include "cntzrecd.mm"
include "riota2.mm"
include "mpbid.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "rexlimddv.mm"

theorem pj1id
  let wph: wff ph
  let cP: class P
  let c.pl: class .+
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cG: class G
  let cX: class X
  let c.0: class .0.
  let cZ: class Z
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume pj1eu.a: |- .+ = ( +g ` G )
  assume pj1eu.s: |- .(+) = ( LSSum ` G )
  assume pj1eu.o: |- .0. = ( 0g ` G )
  assume pj1eu.z: |- Z = ( Cntz ` G )
  assume pj1eu.2: |- ( ph -> T e. ( SubGrp ` G ) )
  assume pj1eu.3: |- ( ph -> U e. ( SubGrp ` G ) )
  assume pj1eu.4: |- ( ph -> ( T i^i U ) = { .0. } )
  assume pj1eu.5: |- ( ph -> T C_ ( Z ` U ) )
  assume pj1f.p: |- P = ( proj1 ` G )


  assert |- ( ( ph /\ X e. ( T .(+) U ) ) -> X = ( ( ( T P U ) ` X ) .+ ( ( U P T ) ` X ) ) )

  proof
    wph
    cX
    cT
    cU
    c.po
    co
    #
    wcel
    #
    wa
    #
    cX
    cX
    cT
    cU
    cP
    co
    #
    cfv
    #
    vy
    cv
    #
    c.pl
    co
    #
    wceq
    #
    cX
    @4
    cX
    cU
    cT
    cP
    co
    cfv
    #
    c.pl
    co
    #
    wceq
    vy
    cU
    @2
    @4
    cX
    vx
    cv
    #
    @5
    c.pl
    co
    #
    wceq
    #
    vy
    cU
    wrex
    #
    vx
    cT
    crab
    #
    wcel
    #
    @7
    vy
    cU
    wrex
    #
    @2
    @4
    @13
    vx
    cT
    crio
    #
    @14
    wph
    cG
    cgrp
    wcel
    #
    cT
    cG
    cbs
    cfv
    #
    wss
    #
    cU
    @19
    wss
    #
    w3a
    @1
    @4
    @17
    wceq
    wph
    @18
    @20
    @21
    wph
    cT
    cG
    csubg
    cfv
    #
    wcel
    #
    @18
    pj1eu.2
    cT
    cG
    subgrcl
    syl
    #
    wph
    @23
    @20
    pj1eu.2
    @19
    cT
    cG
    @19
    eqid
    #
    subgss
    syl
    #
    wph
    cU
    @22
    wcel
    #
    @21
    pj1eu.3
    @19
    cU
    cG
    @25
    subgss
    syl
    #
    3jca
    vx
    vy
    @19
    cP
    c.pl
    c.po
    cT
    cU
    cG
    cgrp
    cX
    @25
    pj1eu.a
    pj1eu.s
    pj1f.p
    pj1val
    sylan
    @2
    @13
    vx
    cT
    wreu
    @17
    @14
    wcel
    wph
    vx
    vy
    c.pl
    c.po
    cT
    cU
    cG
    cX
    c.0
    cZ
    pj1eu.a
    pj1eu.s
    pj1eu.o
    pj1eu.z
    pj1eu.2
    pj1eu.3
    pj1eu.4
    pj1eu.5
    pj1eu
    @13
    vx
    cT
    riotacl2
    syl
    eqeltrd
    @15
    @4
    cT
    wcel
    #
    @16
    @13
    @16
    vx
    @4
    cT
    @10
    @4
    wceq
    #
    @12
    @7
    vy
    cU
    @30
    @11
    @6
    cX
    @10
    @4
    @5
    c.pl
    oveq1
    eqeq2d
    rexbidv
    elrab
    simprbi
    syl
    @2
    @5
    cU
    wcel
    #
    @7
    wa
    #
    wa
    #
    cX
    @6
    @9
    @2
    @31
    @7
    simprr
    #
    @33
    @8
    @5
    @4
    c.pl
    @33
    @8
    cX
    vu
    cv
    #
    vv
    cv
    #
    c.pl
    co
    #
    wceq
    #
    vv
    cT
    wrex
    #
    vu
    cU
    crio
    #
    @5
    @33
    @18
    @21
    @20
    cX
    cU
    cT
    c.po
    co
    #
    wcel
    #
    @8
    @40
    wceq
    wph
    @18
    @1
    @32
    @24
    ad2antrr
    wph
    @21
    @1
    @32
    @28
    ad2antrr
    wph
    @20
    @1
    @32
    @26
    ad2antrr
    @33
    cX
    @0
    @41
    wph
    @1
    @32
    simplr
    #
    wph
    @0
    @41
    wceq
    #
    @1
    @32
    wph
    @23
    @27
    cT
    cU
    cZ
    cfv
    #
    wss
    #
    @44
    pj1eu.2
    pj1eu.3
    pj1eu.5
    c.po
    cT
    cU
    cG
    cZ
    pj1eu.s
    pj1eu.z
    lsmcom2
    syl3anc
    ad2antrr
    eleqtrd
    #
    vu
    vv
    @19
    cP
    c.pl
    c.po
    cU
    cT
    cG
    cgrp
    cX
    @25
    pj1eu.a
    pj1eu.s
    pj1f.p
    pj1val
    syl31anc
    @33
    cX
    @5
    @36
    c.pl
    co
    #
    wceq
    #
    vv
    cT
    wrex
    #
    @40
    @5
    wceq
    #
    @33
    @29
    cX
    @5
    @4
    c.pl
    co
    #
    wceq
    #
    @50
    @33
    @0
    cT
    cX
    @3
    wph
    @0
    cT
    @3
    wf
    @1
    @32
    wph
    cP
    c.pl
    c.po
    cT
    cU
    cG
    c.0
    cZ
    pj1eu.a
    pj1eu.s
    pj1eu.o
    pj1eu.z
    pj1eu.2
    pj1eu.3
    pj1eu.4
    pj1eu.5
    pj1f.p
    pj1f
    ad2antrr
    @43
    ffvelrnd
    #
    @33
    cX
    @6
    @52
    @34
    @33
    @4
    @45
    wcel
    @31
    @6
    @52
    wceq
    @33
    cT
    @45
    @4
    wph
    @46
    @1
    @32
    pj1eu.5
    ad2antrr
    @54
    sseldd
    @2
    @31
    @7
    simprl
    #
    c.pl
    cU
    cG
    @4
    @5
    cZ
    pj1eu.a
    pj1eu.z
    cntzi
    syl2anc
    eqtrd
    @49
    @53
    vv
    @4
    cT
    @36
    @4
    wceq
    @48
    @52
    cX
    @36
    @4
    @5
    c.pl
    oveq2
    eqeq2d
    rspcev
    syl2anc
    @33
    @31
    @39
    vu
    cU
    wreu
    #
    @50
    @51
    wb
    @55
    @33
    wph
    @42
    @56
    wph
    @1
    @32
    simpll
    @47
    wph
    vu
    vv
    c.pl
    c.po
    cU
    cT
    cG
    cX
    c.0
    cZ
    pj1eu.a
    pj1eu.s
    pj1eu.o
    pj1eu.z
    pj1eu.3
    pj1eu.2
    wph
    cU
    cT
    cin
    cT
    cU
    cin
    c.0
    csn
    cU
    cT
    incom
    pj1eu.4
    syl5eq
    wph
    cT
    cU
    cG
    cZ
    pj1eu.z
    pj1eu.2
    pj1eu.3
    pj1eu.5
    cntzrecd
    pj1eu
    syl2anc
    @39
    @50
    vu
    cU
    @5
    @35
    @5
    wceq
    #
    @38
    @49
    vv
    cT
    @57
    @37
    @48
    cX
    @35
    @5
    @36
    c.pl
    oveq1
    eqeq2d
    rexbidv
    riota2
    syl2anc
    mpbid
    eqtrd
    oveq2d
    eqtr4d
    rexlimddv
end
