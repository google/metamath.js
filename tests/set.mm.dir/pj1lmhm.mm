include "co.mm"
include "cress.mm"
include "clmhm.mm"
include "wcel.mm"
include "cghm.mm"
include "csca.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cvsca.mm"
include "cbs.mm"
include "wral.mm"
include "cplusg.mm"
include "ccntz.mm"
include "eqid.mm"
include "csubg.mm"
include "clmod.mm"
include "wss.mm"
include "lsssssubg.mm"
include "syl.mm"
include "sseldd.mm"
include "cabl.mm"
include "lmodabl.mm"
include "ablcntzd.mm"
include "pj1ghm.mm"
include "a1i.mm"
include "wa.mm"
include "pj1id.mm"
include "adantrl.mm"
include "oveq2d.mm"
include "adantr.mm"
include "simprl.mm"
include "lssss.mm"
include "cin.mm"
include "csn.mm"
include "pj1f.mm"
include "simprr.mm"
include "ffvelrnd.mm"
include "pj2f.mm"
include "lmodvsdi.mm"
include "syl13anc.mm"
include "eqtrd.mm"
include "lsmcl.mm"
include "syl3anc.mm"
include "lssvscl.mm"
include "syl22anc.mm"
include "pj1eq.mm"
include "mpbid.mm"
include "simpld.mm"
include "ralrimivva.mm"
include "subgbas.mm"
include "raleqdv.mm"
include "ralbidv.mm"
include "w3a.mm"
include "wb.mm"
include "lsslmod.mm"
include "syl2anc.mm"
include "cvv.mm"
include "ovex.mm"
include "resssca.mm"
include "ax-mp.mm"
include "ressvsca.mm"
include "islmhm3.mm"
include "mpbir3and.mm"

theorem pj1lmhm
  let wph: wff ph
  let cP: class P
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cL: class L
  let cW: class W
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume pj1lmhm.l: |- L = ( LSubSp ` W )
  assume pj1lmhm.s: |- .(+) = ( LSSum ` W )
  assume pj1lmhm.z: |- .0. = ( 0g ` W )
  assume pj1lmhm.p: |- P = ( proj1 ` W )
  assume pj1lmhm.1: |- ( ph -> W e. LMod )
  assume pj1lmhm.2: |- ( ph -> T e. L )
  assume pj1lmhm.3: |- ( ph -> U e. L )
  assume pj1lmhm.4: |- ( ph -> ( T i^i U ) = { .0. } )


  assert |- ( ph -> ( T P U ) e. ( ( W |`s ( T .(+) U ) ) LMHom W ) )

  proof
    wph
    cT
    cU
    cP
    co
    #
    cW
    cT
    cU
    c.po
    co
    #
    cress
    co
    #
    cW
    clmhm
    co
    wcel
    #
    @0
    @2
    cW
    cghm
    co
    wcel
    #
    cW
    csca
    cfv
    #
    @5
    wceq
    #
    vx
    cv
    #
    vy
    cv
    #
    cW
    cvsca
    cfv
    #
    co
    #
    @0
    cfv
    @7
    @8
    @0
    cfv
    #
    @9
    co
    #
    wceq
    #
    vy
    @2
    cbs
    cfv
    #
    wral
    #
    vx
    @5
    cbs
    cfv
    #
    wral
    #
    wph
    cP
    cW
    cplusg
    cfv
    #
    c.po
    cT
    cU
    cW
    c.0
    cW
    ccntz
    cfv
    #
    @18
    eqid
    #
    pj1lmhm.s
    pj1lmhm.z
    @19
    eqid
    #
    wph
    cL
    cW
    csubg
    cfv
    #
    cT
    wph
    cW
    clmod
    wcel
    #
    cL
    @22
    wss
    pj1lmhm.1
    cL
    cW
    pj1lmhm.l
    lsssssubg
    syl
    #
    pj1lmhm.2
    sseldd
    #
    wph
    cL
    @22
    cU
    @24
    pj1lmhm.3
    sseldd
    #
    pj1lmhm.4
    wph
    cT
    cU
    cW
    @19
    @21
    wph
    @23
    cW
    cabl
    wcel
    pj1lmhm.1
    cW
    lmodabl
    syl
    @25
    @26
    ablcntzd
    #
    pj1lmhm.p
    pj1ghm
    @6
    wph
    @5
    eqid
    #
    a1i
    wph
    @13
    vy
    @1
    wral
    #
    vx
    @16
    wral
    @17
    wph
    @13
    vx
    vy
    @16
    @1
    wph
    @7
    @16
    wcel
    #
    @8
    @1
    wcel
    #
    wa
    #
    wa
    #
    @13
    @10
    cU
    cT
    cP
    co
    #
    cfv
    @7
    @8
    @34
    cfv
    #
    @9
    co
    #
    wceq
    #
    @33
    @10
    @12
    @36
    @18
    co
    #
    wceq
    @13
    @37
    wa
    @33
    @10
    @7
    @11
    @35
    @18
    co
    #
    @9
    co
    #
    @38
    @33
    @8
    @39
    @7
    @9
    wph
    @31
    @8
    @39
    wceq
    @30
    wph
    cP
    @18
    c.po
    cT
    cU
    cW
    @8
    c.0
    @19
    @20
    pj1lmhm.s
    pj1lmhm.z
    @21
    @25
    @26
    pj1lmhm.4
    @27
    pj1lmhm.p
    pj1id
    adantrl
    oveq2d
    @33
    @23
    @30
    @11
    cW
    cbs
    cfv
    #
    wcel
    @35
    @41
    wcel
    @40
    @38
    wceq
    wph
    @23
    @32
    pj1lmhm.1
    adantr
    #
    wph
    @30
    @31
    simprl
    #
    @33
    cT
    @41
    @11
    @33
    cT
    cL
    wcel
    #
    cT
    @41
    wss
    wph
    @44
    @32
    pj1lmhm.2
    adantr
    #
    cL
    cT
    @41
    cW
    @41
    eqid
    #
    pj1lmhm.l
    lssss
    syl
    @33
    @1
    cT
    @8
    @0
    @33
    cP
    @18
    c.po
    cT
    cU
    cW
    c.0
    @19
    @20
    pj1lmhm.s
    pj1lmhm.z
    @21
    wph
    cT
    @22
    wcel
    @32
    @25
    adantr
    #
    wph
    cU
    @22
    wcel
    @32
    @26
    adantr
    #
    wph
    cT
    cU
    cin
    c.0
    csn
    wceq
    @32
    pj1lmhm.4
    adantr
    #
    wph
    cT
    cU
    @19
    cfv
    wss
    @32
    @27
    adantr
    #
    pj1lmhm.p
    pj1f
    wph
    @30
    @31
    simprr
    #
    ffvelrnd
    #
    sseldd
    @33
    cU
    @41
    @35
    @33
    cU
    cL
    wcel
    #
    cU
    @41
    wss
    wph
    @53
    @32
    pj1lmhm.3
    adantr
    #
    cL
    cU
    @41
    cW
    @46
    pj1lmhm.l
    lssss
    syl
    @33
    @1
    cU
    @8
    @34
    @33
    cP
    @18
    c.po
    cT
    cU
    cW
    c.0
    @19
    @20
    pj1lmhm.s
    pj1lmhm.z
    @21
    @47
    @48
    @49
    @50
    pj1lmhm.p
    pj2f
    @51
    ffvelrnd
    #
    sseldd
    @18
    @7
    @9
    @5
    @16
    @41
    cW
    @11
    @35
    @46
    @20
    @28
    @9
    eqid
    #
    @16
    eqid
    #
    lmodvsdi
    syl13anc
    eqtrd
    @33
    @12
    @36
    cP
    @18
    c.po
    cT
    cU
    cW
    @10
    c.0
    @19
    @20
    pj1lmhm.s
    pj1lmhm.z
    @21
    @47
    @48
    @49
    @50
    pj1lmhm.p
    @33
    @23
    @1
    cL
    wcel
    #
    @30
    @31
    @10
    @1
    wcel
    @42
    wph
    @58
    @32
    wph
    @23
    @44
    @53
    @58
    pj1lmhm.1
    pj1lmhm.2
    pj1lmhm.3
    c.po
    cL
    cT
    cU
    cW
    pj1lmhm.l
    pj1lmhm.s
    lsmcl
    syl3anc
    #
    adantr
    @43
    @51
    @16
    cL
    @9
    @1
    @5
    cW
    @7
    @8
    @28
    @56
    @57
    pj1lmhm.l
    lssvscl
    syl22anc
    @33
    @23
    @44
    @30
    @11
    cT
    wcel
    @12
    cT
    wcel
    @42
    @45
    @43
    @52
    @16
    cL
    @9
    cT
    @5
    cW
    @7
    @11
    @28
    @56
    @57
    pj1lmhm.l
    lssvscl
    syl22anc
    @33
    @23
    @53
    @30
    @35
    cU
    wcel
    @36
    cU
    wcel
    @42
    @54
    @43
    @55
    @16
    cL
    @9
    cU
    @5
    cW
    @7
    @35
    @28
    @56
    @57
    pj1lmhm.l
    lssvscl
    syl22anc
    pj1eq
    mpbid
    simpld
    ralrimivva
    wph
    @29
    @15
    vx
    @16
    wph
    @13
    vy
    @1
    @14
    wph
    @1
    @22
    wcel
    @1
    @14
    wceq
    wph
    cL
    @22
    @1
    @24
    @59
    sseldd
    @1
    cW
    @2
    @2
    eqid
    #
    subgbas
    syl
    raleqdv
    ralbidv
    mpbid
    wph
    @2
    clmod
    wcel
    #
    @23
    @3
    @4
    @6
    @17
    w3a
    wb
    wph
    @23
    @58
    @61
    pj1lmhm.1
    @59
    cL
    @1
    cW
    @2
    @60
    pj1lmhm.l
    lsslmod
    syl2anc
    pj1lmhm.1
    vx
    vy
    @16
    @2
    cW
    @9
    @9
    @14
    @0
    @5
    @5
    @1
    cvv
    wcel
    #
    @5
    @2
    csca
    cfv
    wceq
    cT
    cU
    c.po
    ovex
    #
    @1
    @5
    cW
    @2
    cvv
    @60
    @28
    resssca
    ax-mp
    @28
    @57
    @14
    eqid
    @62
    @9
    @2
    cvsca
    cfv
    wceq
    @63
    @1
    @9
    cW
    @2
    cvv
    @60
    @56
    ressvsca
    ax-mp
    @56
    islmhm3
    syl2anc
    mpbir3and
end
