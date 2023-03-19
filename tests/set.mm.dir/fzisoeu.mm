include "cfz.mm"
include "co.mm"
include "clt.mm"
include "cv.mm"
include "wiso.mm"
include "wex.mm"
include "wmo.mm"
include "weu.mm"
include "ccnv.mm"
include "ccom.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "wa.mm"
include "wor.mm"
include "cfn.mm"
include "wcel.mm"
include "cr.mm"
include "wss.mm"
include "cz.mm"
include "fzssz.mm"
include "zssre.mm"
include "sstri.mm"
include "ltso.mm"
include "soss.mm"
include "mp2.mm"
include "fzfi.mm"
include "fz1iso.mm"
include "mp2an.mm"
include "wceq.mm"
include "wb.mm"
include "c0.mm"
include "cc0.mm"
include "cmin.mm"
include "caddc.mm"
include "fveq2.mm"
include "hash0.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "adantl.mm"
include "zcnd.mm"
include "1cnd.mm"
include "subcld.mm"
include "addid2d.mm"
include "wbr.mm"
include "zred.mm"
include "ltm1d.mm"
include "peano2zm.mm"
include "syl.mm"
include "fzn.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "eqtrd.mm"
include "adantr.mm"
include "eqcom.mm"
include "biimpi.mm"
include "3eqtrd.mm"
include "fveq2d.mm"
include "wn.mm"
include "cneg.mm"
include "cuz.mm"
include "cle.mm"
include "pncan3d.mm"
include "eqcomd.mm"
include "1red.mm"
include "cn.mm"
include "wne.mm"
include "neqne.mm"
include "hashnncl.mm"
include "mpbird.mm"
include "nnred.mm"
include "nnge1d.mm"
include "leadd1dd.mm"
include "syl6breqr.mm"
include "eqbrtrd.mm"
include "cn0.mm"
include "hashcl.mm"
include "nn0z.mm"
include "3syl.mm"
include "zaddcld.mm"
include "syl5eqel.mm"
include "eluz.mm"
include "hashfz.mm"
include "oveq1i.mm"
include "nn0cnd.mm"
include "addsubassd.mm"
include "negsubd.mm"
include "negcld.mm"
include "pncan2d.mm"
include "npcand.mm"
include "pm2.61dan.mm"
include "isoeq4.mm"
include "biimpd.mm"
include "eximdv.mm"
include "mpi.mm"
include "eeanv.mm"
include "sylanbrc.mm"
include "isocnv.mm"
include "ad2antrl.mm"
include "simprr.mm"
include "isotr.mm"
include "ex.mm"
include "2eximdv.mm"
include "mpd.mm"
include "wi.mm"
include "vex.mm"
include "cnvex.mm"
include "coex.mm"
include "isoeq1.mm"
include "spcev.mm"
include "a1i.mm"
include "exlimdvv.mm"
include "wwe.mm"
include "ltwefz.mm"
include "wemoiso.mm"
include "mp1i.mm"
include "eu5.mm"

theorem fzisoeu
  let wph: wff ph
  let vf: setvar f
  let cH: class H
  let cM: class M
  let cN: class N
  let vg: setvar g
  let vh: setvar h
  assume fzisoeu.h: |- ( ph -> H e. Fin )
  assume fzisoeu.or: |- ( ph -> < Or H )
  assume fzisoeu.m: |- ( ph -> M e. ZZ )
  assume fzisoeu.4: |- N = ( ( # ` H ) + ( M - 1 ) )

  disjoint H f
  disjoint M f
  disjoint N f
  disjoint H g
  disjoint H h
  disjoint f g
  disjoint f h
  disjoint g h
  disjoint M g
  disjoint M h
  disjoint N g
  disjoint N h
  disjoint g ph
  disjoint h ph
  assert |- ( ph -> E! f f Isom < , < ( ( M ... N ) , H ) )

  proof
    wph
    cM
    cN
    cfz
    co
    #
    cH
    clt
    clt
    vf
    cv
    #
    wiso
    #
    vf
    wex
    #
    @2
    vf
    wmo
    #
    @2
    vf
    weu
    wph
    @0
    cH
    clt
    clt
    vg
    cv
    #
    vh
    cv
    #
    ccnv
    #
    ccom
    #
    wiso
    #
    vg
    wex
    vh
    wex
    #
    @3
    wph
    c1
    cH
    chash
    cfv
    #
    cfz
    co
    #
    @0
    clt
    clt
    @6
    wiso
    #
    @12
    cH
    clt
    clt
    @5
    wiso
    #
    wa
    #
    vg
    wex
    vh
    wex
    #
    @10
    wph
    @13
    vh
    wex
    #
    @14
    vg
    wex
    #
    @16
    wph
    c1
    @0
    chash
    cfv
    #
    cfz
    co
    #
    @0
    clt
    clt
    @6
    wiso
    #
    vh
    wex
    #
    @17
    @0
    clt
    wor
    #
    @0
    cfn
    wcel
    @22
    @0
    cr
    wss
    cr
    clt
    wor
    @23
    @0
    cz
    cr
    cM
    cN
    fzssz
    zssre
    sstri
    ltso
    @0
    cr
    clt
    soss
    mp2
    cM
    cN
    fzfi
    @0
    clt
    vh
    fz1iso
    mp2an
    wph
    @21
    @13
    vh
    wph
    @21
    @13
    wph
    @20
    @12
    wceq
    @21
    @13
    wb
    wph
    @19
    @11
    c1
    cfz
    wph
    cH
    c0
    wceq
    #
    @19
    @11
    wceq
    wph
    @24
    wa
    #
    @0
    cH
    chash
    @25
    @0
    cM
    cc0
    cM
    c1
    cmin
    co
    #
    caddc
    co
    #
    cfz
    co
    #
    c0
    cH
    @24
    @0
    @28
    wceq
    wph
    @24
    cN
    @27
    cM
    cfz
    @24
    cN
    @11
    @26
    caddc
    co
    #
    @27
    fzisoeu.4
    @24
    @11
    cc0
    @26
    caddc
    @24
    @11
    c0
    chash
    cfv
    cc0
    cH
    c0
    chash
    fveq2
    hash0
    syl6eq
    oveq1d
    syl5eq
    oveq2d
    adantl
    wph
    @28
    c0
    wceq
    @24
    wph
    @28
    cM
    @26
    cfz
    co
    #
    c0
    wph
    @27
    @26
    cM
    cfz
    wph
    @26
    wph
    cM
    c1
    wph
    cM
    fzisoeu.m
    zcnd
    #
    wph
    1cnd
    #
    subcld
    #
    addid2d
    oveq2d
    wph
    @26
    cM
    clt
    wbr
    #
    @30
    c0
    wceq
    #
    wph
    cM
    wph
    cM
    fzisoeu.m
    zred
    ltm1d
    wph
    cM
    cz
    wcel
    #
    @26
    cz
    wcel
    #
    @34
    @35
    wb
    fzisoeu.m
    wph
    @36
    @37
    fzisoeu.m
    cM
    peano2zm
    syl
    #
    cM
    @26
    fzn
    syl2anc
    mpbid
    eqtrd
    adantr
    @24
    c0
    cH
    wceq
    #
    wph
    @24
    @39
    cH
    c0
    eqcom
    biimpi
    adantl
    3eqtrd
    fveq2d
    wph
    @24
    wn
    #
    wa
    #
    @19
    cN
    cM
    cmin
    co
    #
    c1
    caddc
    co
    #
    @11
    c1
    cneg
    #
    caddc
    co
    #
    c1
    caddc
    co
    #
    @11
    @41
    cN
    cM
    cuz
    cfv
    wcel
    #
    @19
    @43
    wceq
    @41
    @47
    cM
    cN
    cle
    wbr
    #
    @41
    cM
    c1
    @26
    caddc
    co
    #
    cN
    cle
    wph
    cM
    @49
    wceq
    @40
    wph
    @49
    cM
    wph
    c1
    cM
    @32
    @31
    pncan3d
    eqcomd
    adantr
    @41
    @49
    @29
    cN
    cle
    @41
    c1
    @11
    @26
    @41
    1red
    @41
    @11
    @41
    @11
    cn
    wcel
    #
    cH
    c0
    wne
    #
    @40
    @51
    wph
    cH
    c0
    neqne
    adantl
    @41
    cH
    cfn
    wcel
    #
    @50
    @51
    wb
    wph
    @52
    @40
    fzisoeu.h
    adantr
    cH
    hashnncl
    syl
    mpbird
    #
    nnred
    wph
    @26
    cr
    wcel
    @40
    wph
    @26
    @38
    zred
    adantr
    @41
    @11
    @53
    nnge1d
    leadd1dd
    fzisoeu.4
    syl6breqr
    eqbrtrd
    @41
    @36
    cN
    cz
    wcel
    #
    @47
    @48
    wb
    wph
    @36
    @40
    fzisoeu.m
    adantr
    wph
    @54
    @40
    wph
    cN
    @29
    cz
    fzisoeu.4
    wph
    @11
    @26
    wph
    @52
    @11
    cn0
    wcel
    #
    @11
    cz
    wcel
    fzisoeu.h
    cH
    hashcl
    #
    @11
    nn0z
    3syl
    @38
    zaddcld
    syl5eqel
    adantr
    cM
    cN
    eluz
    syl2anc
    mpbird
    cM
    cN
    hashfz
    syl
    wph
    @43
    @46
    wceq
    @40
    wph
    @42
    @45
    c1
    caddc
    wph
    @42
    @11
    @26
    cM
    cmin
    co
    #
    caddc
    co
    #
    @45
    wph
    @42
    @29
    cM
    cmin
    co
    @58
    cN
    @29
    cM
    cmin
    fzisoeu.4
    oveq1i
    wph
    @11
    @26
    cM
    wph
    @11
    wph
    @52
    @55
    fzisoeu.h
    @56
    syl
    nn0cnd
    #
    @33
    @31
    addsubassd
    syl5eq
    wph
    @57
    @44
    @11
    caddc
    wph
    @57
    cM
    @44
    caddc
    co
    #
    cM
    cmin
    co
    @44
    wph
    @26
    @60
    cM
    cmin
    wph
    @60
    @26
    wph
    cM
    c1
    @31
    @32
    negsubd
    eqcomd
    oveq1d
    wph
    cM
    @44
    @31
    wph
    c1
    @32
    negcld
    pncan2d
    eqtrd
    oveq2d
    eqtrd
    oveq1d
    adantr
    wph
    @46
    @11
    wceq
    @40
    wph
    @46
    @11
    c1
    cmin
    co
    #
    c1
    caddc
    co
    @11
    wph
    @45
    @61
    c1
    caddc
    wph
    @11
    c1
    @59
    @32
    negsubd
    oveq1d
    wph
    @11
    c1
    @59
    @32
    npcand
    eqtrd
    adantr
    3eqtrd
    pm2.61dan
    oveq2d
    @20
    @0
    @12
    clt
    clt
    @6
    isoeq4
    syl
    biimpd
    eximdv
    mpi
    wph
    cH
    clt
    wor
    @52
    @18
    fzisoeu.or
    fzisoeu.h
    cH
    clt
    vg
    fz1iso
    syl2anc
    @13
    @14
    vh
    vg
    eeanv
    sylanbrc
    wph
    @15
    @9
    vh
    vg
    wph
    @15
    @9
    wph
    @15
    wa
    @0
    @12
    clt
    clt
    @7
    wiso
    #
    @14
    @9
    @13
    @62
    wph
    @14
    @12
    @0
    clt
    clt
    @6
    isocnv
    ad2antrl
    wph
    @13
    @14
    simprr
    @0
    @12
    cH
    clt
    clt
    clt
    @5
    @7
    isotr
    syl2anc
    ex
    2eximdv
    mpd
    wph
    @9
    @3
    vh
    vg
    @9
    @3
    wi
    wph
    @2
    @9
    vf
    @8
    @5
    @7
    vg
    vex
    @6
    vh
    vex
    cnvex
    coex
    @0
    cH
    clt
    clt
    @8
    @1
    isoeq1
    spcev
    a1i
    exlimdvv
    mpd
    @0
    clt
    wwe
    @4
    wph
    cM
    cN
    ltwefz
    @0
    cH
    clt
    clt
    vf
    wemoiso
    mp1i
    @2
    vf
    eu5
    sylanbrc
end
