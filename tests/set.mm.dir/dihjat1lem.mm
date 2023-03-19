include "csn.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "oveq1d.mm"
include "chlt.mm"
include "wcel.mm"
include "crn.mm"
include "cdif.mm"
include "eldifi.mm"
include "syl.mm"
include "dihlsprn.mm"
include "syl2anc.mm"
include "djh02.mm"
include "csubg.mm"
include "clmod.mm"
include "clss.mm"
include "dvhlmod.mm"
include "eqid.mm"
include "lspsncl.mm"
include "lsssubg.mm"
include "lsm02.mm"
include "eqtr4d.mm"
include "adantr.mm"
include "wne.mm"
include "wss.mm"
include "dihrnss.mm"
include "lssss.mm"
include "djhcl.mm"
include "syl12anc.mm"
include "dihrnlss.mm"
include "lsmcl.mm"
include "syl3anc.mm"
include "cv.mm"
include "wrex.mm"
include "simplr.mm"
include "ad2antrr.mm"
include "djhcvat42.mm"
include "mpand.mm"
include "simprrl.mm"
include "ad3antrrr.mm"
include "ad2antrl.mm"
include "lspsnel5.mm"
include "mpbird.mm"
include "lspsnid.mm"
include "simprrr.mm"
include "sneq.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "sseq2d.mm"
include "rspcev.mm"
include "jca.mm"
include "ex.mm"
include "reximdv2.mm"
include "syld.mm"
include "anim2d.mm"
include "wb.mm"
include "lspsnel6.mm"
include "lsmelval2.mm"
include "lssel.mm"
include "djhlsmat.mm"
include "rexbidva.mm"
include "anbi2d.mm"
include "bitrd.mm"
include "3imtr4d.mm"
include "lssssr.mm"
include "djhsumss.mm"
include "eqssd.mm"
include "pm2.61dane.mm"

theorem dihjat1lem
  let wph: wff ph
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vy: setvar y
  let vx: setvar x
  let vz: setvar z
  assume dihjat1.h: |- H = ( LHyp ` K )
  assume dihjat1.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihjat1.v: |- V = ( Base ` U )
  assume dihjat1.p: |- .(+) = ( LSSum ` U )
  assume dihjat1.n: |- N = ( LSpan ` U )
  assume dihjat1.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihjat1.j: |- .\/ = ( ( joinH ` K ) ` W )
  assume dihjat1.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dihjat1.x: |- ( ph -> X e. ran I )
  assume dihjat1.o: |- .0. = ( 0g ` U )
  assume dihjat1lem.q: |- ( ph -> T e. ( V \ { .0. } ) )


  assert |- ( ph -> ( X .\/ ( N ` { T } ) ) = ( X .(+) ( N ` { T } ) ) )

  proof
    wph
    cX
    cT
    csn
    #
    cN
    cfv
    #
    c.or
    co
    #
    cX
    @1
    c.po
    co
    #
    wceq
    cX
    c.0
    csn
    #
    wph
    cX
    @4
    wceq
    #
    wa
    #
    @2
    @4
    @1
    c.or
    co
    #
    @3
    @6
    cX
    @4
    @1
    c.or
    wph
    @5
    simpr
    #
    oveq1d
    @6
    @3
    @4
    @1
    c.po
    co
    #
    @7
    @6
    cX
    @4
    @1
    c.po
    @8
    oveq1d
    wph
    @7
    @9
    wceq
    @5
    wph
    @7
    @1
    @9
    wph
    cU
    cH
    cI
    c.or
    cK
    cW
    @1
    c.0
    dihjat1.h
    dihjat1.u
    dihjat1.o
    dihjat1.i
    dihjat1.j
    dihjat1.k
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cT
    cV
    wcel
    #
    @1
    cI
    crn
    #
    wcel
    dihjat1.k
    wph
    cT
    cV
    @4
    cdif
    #
    wcel
    #
    @11
    dihjat1lem.q
    cT
    cV
    @4
    eldifi
    syl
    #
    cU
    cH
    cI
    cK
    cN
    cV
    cW
    cT
    dihjat1.h
    dihjat1.u
    dihjat1.v
    dihjat1.n
    dihjat1.i
    dihlsprn
    syl2anc
    djh02
    wph
    @1
    cU
    csubg
    cfv
    wcel
    #
    @9
    @1
    wceq
    wph
    cU
    clmod
    wcel
    #
    @1
    cU
    clss
    cfv
    #
    wcel
    #
    @16
    wph
    cU
    cH
    cK
    cW
    dihjat1.h
    dihjat1.u
    dihjat1.k
    dvhlmod
    #
    wph
    @17
    @11
    @19
    @20
    @15
    @18
    cN
    cV
    cU
    cT
    dihjat1.v
    @18
    eqid
    #
    dihjat1.n
    lspsncl
    syl2anc
    #
    @18
    @1
    cU
    @21
    lsssubg
    syl2anc
    c.po
    cU
    @1
    c.0
    dihjat1.o
    dihjat1.p
    lsm02
    syl
    eqtr4d
    adantr
    eqtr4d
    eqtr4d
    wph
    cX
    @4
    wne
    #
    wa
    #
    @2
    @3
    @24
    vx
    @18
    @2
    @3
    cV
    cU
    c.0
    dihjat1.v
    dihjat1.o
    @21
    wph
    @17
    @23
    @20
    adantr
    wph
    @2
    cV
    wss
    #
    @23
    wph
    @10
    @2
    @12
    wcel
    #
    @25
    dihjat1.k
    wph
    @10
    cX
    cV
    wss
    #
    @1
    cV
    wss
    #
    @26
    dihjat1.k
    wph
    @10
    cX
    @12
    wcel
    #
    @27
    dihjat1.k
    dihjat1.x
    cU
    cH
    cI
    cK
    cV
    cW
    cX
    dihjat1.h
    dihjat1.u
    dihjat1.i
    dihjat1.v
    dihrnss
    syl2anc
    #
    wph
    @19
    @28
    @22
    @18
    @1
    cV
    cU
    dihjat1.v
    @21
    lssss
    syl
    #
    cU
    cH
    cI
    c.or
    cK
    cV
    cW
    cX
    @1
    dihjat1.h
    dihjat1.i
    dihjat1.u
    dihjat1.v
    dihjat1.j
    djhcl
    syl12anc
    #
    cU
    cH
    cI
    cK
    cV
    cW
    @2
    dihjat1.h
    dihjat1.u
    dihjat1.i
    dihjat1.v
    dihrnss
    syl2anc
    adantr
    wph
    @3
    @18
    wcel
    #
    @23
    wph
    @17
    cX
    @18
    wcel
    #
    @19
    @33
    @20
    wph
    @10
    @29
    @34
    dihjat1.k
    dihjat1.x
    @18
    cU
    cH
    cI
    cK
    cW
    cX
    dihjat1.h
    dihjat1.u
    dihjat1.i
    @21
    dihrnlss
    syl2anc
    #
    @22
    c.po
    @18
    cX
    @1
    cU
    @21
    dihjat1.p
    lsmcl
    syl3anc
    adantr
    @24
    vx
    cv
    #
    @13
    wcel
    #
    wa
    #
    @36
    cV
    wcel
    #
    @36
    csn
    cN
    cfv
    #
    @2
    wss
    #
    wa
    #
    @39
    @40
    vy
    cv
    #
    csn
    cN
    cfv
    #
    vz
    cv
    #
    csn
    #
    cN
    cfv
    #
    c.or
    co
    #
    wss
    #
    vz
    @1
    wrex
    #
    vy
    cX
    wrex
    #
    wa
    #
    @36
    @2
    wcel
    #
    @36
    @3
    wcel
    #
    @38
    @41
    @51
    @39
    @38
    @41
    @44
    cX
    wss
    #
    @40
    @44
    @1
    c.or
    co
    #
    wss
    #
    wa
    #
    vy
    @13
    wrex
    #
    @51
    @38
    @23
    @41
    @59
    wph
    @23
    @37
    simplr
    @38
    vy
    cX
    cU
    cH
    cI
    c.or
    cK
    cN
    cV
    cW
    @36
    cT
    c.0
    dihjat1.h
    dihjat1.u
    dihjat1.v
    dihjat1.o
    dihjat1.n
    dihjat1.i
    dihjat1.j
    wph
    @10
    @23
    @37
    dihjat1.k
    ad2antrr
    wph
    @29
    @23
    @37
    dihjat1.x
    ad2antrr
    @24
    @37
    simpr
    wph
    @14
    @23
    @37
    dihjat1lem.q
    ad2antrr
    djhcvat42
    mpand
    @38
    @58
    @50
    vy
    @13
    cX
    @38
    @43
    @13
    wcel
    #
    @58
    wa
    #
    @43
    cX
    wcel
    #
    @50
    wa
    @38
    @61
    wa
    #
    @62
    @50
    @63
    @62
    @55
    @38
    @60
    @55
    @57
    simprrl
    @63
    @18
    cX
    cN
    cV
    cU
    @43
    dihjat1.v
    @21
    dihjat1.n
    wph
    @17
    @23
    @37
    @61
    @20
    ad3antrrr
    #
    wph
    @34
    @23
    @37
    @61
    @35
    ad3antrrr
    @60
    @43
    cV
    wcel
    #
    @38
    @58
    @43
    cV
    @4
    eldifi
    ad2antrl
    lspsnel5
    mpbird
    @63
    cT
    @1
    wcel
    #
    @57
    @50
    @63
    @17
    @11
    @66
    @64
    wph
    @11
    @23
    @37
    @61
    @15
    ad3antrrr
    cN
    cV
    cU
    cT
    dihjat1.v
    dihjat1.n
    lspsnid
    syl2anc
    @38
    @60
    @55
    @57
    simprrr
    @49
    @57
    vz
    cT
    @1
    @45
    cT
    wceq
    #
    @48
    @56
    @40
    @67
    @47
    @1
    @44
    c.or
    @67
    @46
    @0
    cN
    @45
    cT
    sneq
    fveq2d
    oveq2d
    sseq2d
    rspcev
    syl2anc
    jca
    ex
    reximdv2
    syld
    anim2d
    wph
    @53
    @42
    wb
    @23
    @37
    wph
    @18
    @2
    cN
    cV
    cU
    @36
    dihjat1.v
    @21
    dihjat1.n
    @20
    wph
    @10
    @26
    @2
    @18
    wcel
    dihjat1.k
    @32
    @18
    cU
    cH
    cI
    cK
    cW
    @2
    dihjat1.h
    dihjat1.u
    dihjat1.i
    @21
    dihrnlss
    syl2anc
    lspsnel6
    ad2antrr
    wph
    @54
    @52
    wb
    @23
    @37
    wph
    @54
    @39
    @40
    @44
    @47
    c.po
    co
    #
    wss
    #
    vz
    @1
    wrex
    #
    vy
    cX
    wrex
    #
    wa
    @52
    wph
    vy
    vz
    c.po
    @18
    cX
    @1
    cN
    cV
    cU
    @36
    dihjat1.v
    @21
    dihjat1.p
    dihjat1.n
    @20
    @35
    @22
    lsmelval2
    wph
    @71
    @51
    @39
    wph
    @70
    @50
    vy
    cX
    wph
    @62
    wa
    #
    @69
    @49
    vz
    @1
    @72
    @45
    @1
    wcel
    #
    wa
    #
    @68
    @48
    @40
    @74
    c.po
    cU
    cH
    cI
    c.or
    cK
    cN
    cV
    cW
    @43
    @45
    dihjat1.h
    dihjat1.u
    dihjat1.v
    dihjat1.p
    dihjat1.n
    dihjat1.i
    dihjat1.j
    wph
    @10
    @62
    @73
    dihjat1.k
    ad2antrr
    @74
    @34
    @62
    @65
    wph
    @34
    @62
    @73
    @35
    ad2antrr
    wph
    @62
    @73
    simplr
    @18
    cX
    cV
    cU
    @43
    dihjat1.v
    @21
    lssel
    syl2anc
    @74
    @19
    @73
    @45
    cV
    wcel
    wph
    @19
    @62
    @73
    @22
    ad2antrr
    @72
    @73
    simpr
    @18
    @1
    cV
    cU
    @45
    dihjat1.v
    @21
    lssel
    syl2anc
    djhlsmat
    sseq2d
    rexbidva
    rexbidva
    anbi2d
    bitrd
    ad2antrr
    3imtr4d
    lssssr
    wph
    @3
    @2
    wss
    @23
    wph
    c.po
    cU
    cH
    c.or
    cK
    cV
    cW
    cX
    @1
    dihjat1.h
    dihjat1.u
    dihjat1.v
    dihjat1.p
    dihjat1.j
    dihjat1.k
    @30
    @31
    djhsumss
    adantr
    eqssd
    pm2.61dane
end
