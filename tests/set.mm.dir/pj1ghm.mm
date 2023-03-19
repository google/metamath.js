include "co.mm"
include "cress.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "cvv.mm"
include "wcel.mm"
include "cplusg.mm"
include "wceq.mm"
include "ovex.mm"
include "ressplusg.mm"
include "ax-mp.mm"
include "csubg.mm"
include "cgrp.mm"
include "wss.mm"
include "lsmsubg.mm"
include "syl3anc.mm"
include "subggrp.mm"
include "syl.mm"
include "subgrcl.mm"
include "wf.mm"
include "pj1f.mm"
include "subgss.mm"
include "fssd.mm"
include "subgbas.mm"
include "feq2d.mm"
include "mpbid.mm"
include "cv.mm"
include "wa.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "biimpar.mm"
include "pj1id.mm"
include "adantrr.mm"
include "adantrl.mm"
include "oveq12d.mm"
include "cmnd.mm"
include "adantr.mm"
include "grpmnd.mm"
include "3syl.mm"
include "simpl.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "sseldd.mm"
include "simpr.mm"
include "pj2f.mm"
include "cntzi.mm"
include "syl2anc.mm"
include "mnd4g.mm"
include "eqtr4d.mm"
include "cin.mm"
include "csn.mm"
include "subgcl.mm"
include "3expb.mm"
include "sylan.mm"
include "pj1eq.mm"
include "simpld.mm"
include "syldan.mm"
include "isghmd.mm"

theorem pj1ghm
  let wph: wff ph
  let cP: class P
  let c.pl: class .+
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cG: class G
  let c.0: class .0.
  let cZ: class Z
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cX: class X
  assume pj1eu.a: |- .+ = ( +g ` G )
  assume pj1eu.s: |- .(+) = ( LSSum ` G )
  assume pj1eu.o: |- .0. = ( 0g ` G )
  assume pj1eu.z: |- Z = ( Cntz ` G )
  assume pj1eu.2: |- ( ph -> T e. ( SubGrp ` G ) )
  assume pj1eu.3: |- ( ph -> U e. ( SubGrp ` G ) )
  assume pj1eu.4: |- ( ph -> ( T i^i U ) = { .0. } )
  assume pj1eu.5: |- ( ph -> T C_ ( Z ` U ) )
  assume pj1f.p: |- P = ( proj1 ` G )


  assert |- ( ph -> ( T P U ) e. ( ( G |`s ( T .(+) U ) ) GrpHom G ) )

  proof
    wph
    vx
    vy
    c.pl
    c.pl
    cG
    cT
    cU
    c.po
    co
    #
    cress
    co
    #
    cG
    cT
    cU
    cP
    co
    #
    @1
    cbs
    cfv
    #
    cG
    cbs
    cfv
    #
    @3
    eqid
    @4
    eqid
    #
    @0
    cvv
    wcel
    c.pl
    @1
    cplusg
    cfv
    wceq
    cT
    cU
    c.po
    ovex
    @0
    c.pl
    cG
    @1
    cvv
    @1
    eqid
    #
    pj1eu.a
    ressplusg
    ax-mp
    pj1eu.a
    wph
    @0
    cG
    csubg
    cfv
    #
    wcel
    #
    @1
    cgrp
    wcel
    wph
    cT
    @7
    wcel
    #
    cU
    @7
    wcel
    #
    cT
    cU
    cZ
    cfv
    #
    wss
    #
    @8
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
    lsmsubg
    syl3anc
    #
    @0
    cG
    @1
    @6
    subggrp
    syl
    wph
    @9
    cG
    cgrp
    wcel
    #
    pj1eu.2
    cT
    cG
    subgrcl
    #
    syl
    wph
    @0
    @4
    @2
    wf
    @3
    @4
    @2
    wf
    wph
    @0
    cT
    @4
    @2
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
    #
    wph
    @9
    cT
    @4
    wss
    #
    pj1eu.2
    @4
    cT
    cG
    @5
    subgss
    #
    syl
    fssd
    wph
    @0
    @3
    @4
    @2
    wph
    @8
    @0
    @3
    wceq
    @13
    @0
    cG
    @1
    @6
    subgbas
    syl
    #
    feq2d
    mpbid
    wph
    vx
    cv
    #
    @3
    wcel
    #
    vy
    cv
    #
    @3
    wcel
    #
    wa
    #
    @20
    @0
    wcel
    #
    @22
    @0
    wcel
    #
    wa
    #
    @20
    @22
    c.pl
    co
    #
    @2
    cfv
    @20
    @2
    cfv
    #
    @22
    @2
    cfv
    #
    c.pl
    co
    #
    wceq
    #
    wph
    @27
    @24
    wph
    @25
    @21
    @26
    @23
    wph
    @0
    @3
    @20
    @19
    eleq2d
    wph
    @0
    @3
    @22
    @19
    eleq2d
    anbi12d
    biimpar
    wph
    @27
    wa
    #
    @32
    @28
    cU
    cT
    cP
    co
    #
    cfv
    @20
    @34
    cfv
    #
    @22
    @34
    cfv
    #
    c.pl
    co
    #
    wceq
    #
    @33
    @28
    @31
    @37
    c.pl
    co
    #
    wceq
    @32
    @38
    wa
    @33
    @28
    @29
    @35
    c.pl
    co
    #
    @30
    @36
    c.pl
    co
    #
    c.pl
    co
    @39
    @33
    @20
    @40
    @22
    @41
    c.pl
    wph
    @25
    @20
    @40
    wceq
    @26
    wph
    cP
    c.pl
    c.po
    cT
    cU
    cG
    @20
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
    pj1id
    adantrr
    wph
    @26
    @22
    @41
    wceq
    @25
    wph
    cP
    c.pl
    c.po
    cT
    cU
    cG
    @22
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
    pj1id
    adantrl
    oveq12d
    @33
    @4
    c.pl
    cG
    @36
    @29
    @30
    @35
    @5
    pj1eu.a
    @33
    @9
    @14
    cG
    cmnd
    wcel
    wph
    @9
    @27
    pj1eu.2
    adantr
    #
    @15
    cG
    grpmnd
    3syl
    @33
    cT
    @4
    @29
    @33
    @9
    @17
    @42
    @18
    syl
    #
    wph
    @0
    cT
    @2
    wf
    #
    @25
    @29
    cT
    wcel
    #
    @27
    @16
    @25
    @26
    simpl
    #
    @0
    cT
    @20
    @2
    ffvelrn
    syl2an
    #
    sseldd
    @33
    cT
    @4
    @30
    @43
    wph
    @44
    @26
    @30
    cT
    wcel
    #
    @27
    @16
    @25
    @26
    simpr
    #
    @0
    cT
    @22
    @2
    ffvelrn
    syl2an
    #
    sseldd
    @33
    cU
    @4
    @35
    @33
    @10
    cU
    @4
    wss
    wph
    @10
    @27
    pj1eu.3
    adantr
    #
    @4
    cU
    cG
    @5
    subgss
    syl
    #
    wph
    @0
    cU
    @34
    wf
    #
    @25
    @35
    cU
    wcel
    #
    @27
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
    pj2f
    #
    @46
    @0
    cU
    @20
    @34
    ffvelrn
    syl2an
    #
    sseldd
    @33
    cU
    @4
    @36
    @52
    wph
    @53
    @26
    @36
    cU
    wcel
    #
    @27
    @55
    @49
    @0
    cU
    @22
    @34
    ffvelrn
    syl2an
    #
    sseldd
    @33
    @30
    @11
    wcel
    @54
    @30
    @35
    c.pl
    co
    @35
    @30
    c.pl
    co
    wceq
    @33
    cT
    @11
    @30
    wph
    @12
    @27
    pj1eu.5
    adantr
    #
    @50
    sseldd
    @56
    c.pl
    cU
    cG
    @30
    @35
    cZ
    pj1eu.a
    pj1eu.z
    cntzi
    syl2anc
    mnd4g
    eqtr4d
    @33
    @31
    @37
    cP
    c.pl
    c.po
    cT
    cU
    cG
    @28
    c.0
    cZ
    pj1eu.a
    pj1eu.s
    pj1eu.o
    pj1eu.z
    @42
    @51
    wph
    cT
    cU
    cin
    c.0
    csn
    wceq
    @27
    pj1eu.4
    adantr
    @59
    pj1f.p
    wph
    @8
    @27
    @28
    @0
    wcel
    #
    @13
    @8
    @25
    @26
    @60
    c.pl
    @0
    cG
    @20
    @22
    pj1eu.a
    subgcl
    3expb
    sylan
    @33
    @9
    @45
    @48
    @31
    cT
    wcel
    @42
    @47
    @50
    c.pl
    cT
    cG
    @29
    @30
    pj1eu.a
    subgcl
    syl3anc
    @33
    @10
    @54
    @57
    @37
    cU
    wcel
    @51
    @56
    @58
    c.pl
    cU
    cG
    @35
    @36
    pj1eu.a
    subgcl
    syl3anc
    pj1eq
    mpbid
    simpld
    syldan
    isghmd
end
