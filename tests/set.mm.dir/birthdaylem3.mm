include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cmin.mm"
include "cneg.mm"
include "ce.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cc0.mm"
include "c0.mm"
include "c1.mm"
include "cfz.mm"
include "cv.mm"
include "wf1.mm"
include "cab.mm"
include "wceq.mm"
include "wne.mm"
include "cdom.mm"
include "wn.mm"
include "wex.mm"
include "abn0.mm"
include "ovex.mm"
include "brdom.mm"
include "bitr4i.mm"
include "hashfz1.mm"
include "nnnn0.mm"
include "syl.mm"
include "breqan12d.mm"
include "cfn.mm"
include "wb.mm"
include "fzfid.mm"
include "hashdom.mm"
include "syl2anc.mm"
include "cr.mm"
include "nn0re.mm"
include "nnre.mm"
include "lenlt.mm"
include "syl2an.mm"
include "3bitr3d.mm"
include "syl5bb.mm"
include "necon4abid.mm"
include "biimpar.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "hash0.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "wss.mm"
include "wi.mm"
include "birthdaylem1.mm"
include "simp3i.mm"
include "ad2antlr.mm"
include "simp2i.mm"
include "hashnncl.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "div0d.mm"
include "eqtrd.mm"
include "adantr.mm"
include "resqcld.mm"
include "resubcld.mm"
include "rehalfcld.mm"
include "nndivre.mm"
include "sylancom.mm"
include "renegcld.mm"
include "rpefcld.mm"
include "rpge0d.mm"
include "eqbrtrd.mm"
include "clog.mm"
include "csu.mm"
include "simplr.mm"
include "simpr.mm"
include "cuz.mm"
include "cz.mm"
include "simpll.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "nnz.mm"
include "elfz5.mm"
include "mpbird.mm"
include "birthdaylem2.mm"
include "crp.mm"
include "cmul.mm"
include "elfznn0.mm"
include "adantl.mm"
include "nn0red.mm"
include "peano2rem.mm"
include "nnred.mm"
include "elfzle2.mm"
include "ltm1d.mm"
include "ltletrd.mm"
include "lelttrd.mm"
include "mulid1d.mm"
include "breqtrrd.mm"
include "1red.mm"
include "nngt0d.mm"
include "ltdivmul.mm"
include "syl112anc.mm"
include "nndivred.mm"
include "1re.mm"
include "difrp.mm"
include "sylancl.mm"
include "mpbid.mm"
include "relogcld.mm"
include "elfzle1.mm"
include "divge0.mm"
include "syl22anc.mm"
include "eflegeo.mm"
include "reefcld.mm"
include "efgt0.mm"
include "rpregt0d.mm"
include "lerec2.mm"
include "syl21anc.mm"
include "reeflogd.mm"
include "cc.mm"
include "recnd.mm"
include "efneg.mm"
include "3brtr4d.mm"
include "efle.mm"
include "fsumle.mm"
include "fsumneg.mm"
include "nnne0.mm"
include "fsumdivc.mm"
include "arisum2.mm"
include "eqtr3d.mm"
include "negeqd.mm"
include "breqtrd.mm"
include "fsumrecl.mm"
include "ltlecasei.mm"

theorem birthdaylem3
  let cS: class S
  let cT: class T
  let vf: setvar f
  let cK: class K
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  assume birthday.s: |- S = { f | f : ( 1 ... K ) --> ( 1 ... N ) }
  assume birthday.t: |- T = { f | f : ( 1 ... K ) -1-1-> ( 1 ... N ) }

  disjoint K f
  disjoint N f
  disjoint f k
  disjoint f n
  disjoint k n
  disjoint K k
  disjoint K n
  disjoint N k
  disjoint N n
  assert |- ( ( K e. NN0 /\ N e. NN ) -> ( ( # ` T ) / ( # ` S ) ) <_ ( exp ` -u ( ( ( ( K ^ 2 ) - K ) / 2 ) / N ) ) )

  proof
    cK
    cn0
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    cT
    chash
    cfv
    #
    cS
    chash
    cfv
    #
    cdiv
    co
    #
    cK
    c2
    cexp
    co
    #
    cK
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cN
    cdiv
    co
    #
    cneg
    #
    ce
    cfv
    #
    cle
    wbr
    cN
    cK
    @2
    cN
    cK
    clt
    wbr
    #
    wa
    #
    @5
    cc0
    @11
    cle
    @13
    @5
    cc0
    @4
    cdiv
    co
    cc0
    @13
    @3
    cc0
    @4
    cdiv
    @13
    @3
    c0
    chash
    cfv
    cc0
    @13
    cT
    c0
    chash
    @13
    cT
    c1
    cK
    cfz
    co
    #
    c1
    cN
    cfz
    co
    #
    vf
    cv
    wf1
    #
    vf
    cab
    #
    c0
    birthday.t
    @2
    @17
    c0
    wceq
    @12
    @2
    @12
    @17
    c0
    @17
    c0
    wne
    #
    @14
    @15
    cdom
    wbr
    #
    @2
    @12
    wn
    #
    @18
    @16
    vf
    wex
    @19
    @16
    vf
    abn0
    @14
    @15
    vf
    c1
    cN
    cfz
    ovex
    brdom
    bitr4i
    @2
    @14
    chash
    cfv
    #
    @15
    chash
    cfv
    #
    cle
    wbr
    #
    cK
    cN
    cle
    wbr
    #
    @19
    @20
    @0
    @1
    @21
    cK
    @22
    cN
    cle
    cK
    hashfz1
    @1
    cN
    cn0
    wcel
    @22
    cN
    wceq
    cN
    nnnn0
    cN
    hashfz1
    syl
    breqan12d
    @2
    @14
    cfn
    wcel
    @15
    cfn
    wcel
    @23
    @19
    wb
    @2
    c1
    cK
    fzfid
    @2
    c1
    cN
    fzfid
    @14
    @15
    cfn
    hashdom
    syl2anc
    @0
    cK
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    @24
    @20
    wb
    @1
    cK
    nn0re
    #
    cN
    nnre
    #
    cK
    cN
    lenlt
    syl2an
    3bitr3d
    syl5bb
    necon4abid
    biimpar
    syl5eq
    fveq2d
    hash0
    syl6eq
    oveq1d
    @13
    @4
    @13
    @4
    @13
    cS
    c0
    wne
    #
    @4
    cn
    wcel
    #
    @1
    @29
    @0
    @12
    cT
    cS
    wss
    #
    cS
    cfn
    wcel
    #
    @1
    @29
    wi
    #
    cS
    cT
    vf
    cK
    cN
    birthday.s
    birthday.t
    birthdaylem1
    #
    simp3i
    ad2antlr
    @32
    @30
    @29
    wb
    @31
    @32
    @33
    @34
    simp2i
    cS
    hashnncl
    ax-mp
    sylibr
    #
    nncnd
    @13
    @4
    @35
    nnne0d
    div0d
    eqtrd
    @13
    @11
    @13
    @10
    @2
    @10
    cr
    wcel
    #
    @12
    @2
    @9
    @0
    @1
    @8
    cr
    wcel
    @9
    cr
    wcel
    @2
    @7
    @2
    @6
    cK
    @2
    cK
    @0
    @25
    @1
    @27
    adantr
    #
    resqcld
    @37
    resubcld
    rehalfcld
    @8
    cN
    nndivre
    sylancom
    renegcld
    #
    adantr
    rpefcld
    rpge0d
    eqbrtrd
    @2
    @24
    wa
    #
    @5
    cc0
    cK
    c1
    cmin
    co
    #
    cfz
    co
    #
    c1
    vk
    cv
    #
    cN
    cdiv
    co
    #
    cmin
    co
    #
    clog
    cfv
    #
    vk
    csu
    #
    ce
    cfv
    #
    @11
    cle
    @39
    @1
    cK
    cc0
    cN
    cfz
    co
    wcel
    #
    @5
    @47
    wceq
    @0
    @1
    @24
    simplr
    #
    @39
    @48
    @24
    @2
    @24
    simpr
    #
    @39
    cK
    cc0
    cuz
    cfv
    #
    wcel
    cN
    cz
    wcel
    #
    @48
    @24
    wb
    @39
    cK
    cn0
    @51
    @0
    @1
    @24
    simpll
    #
    nn0uz
    syl6eleq
    @1
    @52
    @0
    @24
    cN
    nnz
    ad2antlr
    cK
    cc0
    cN
    elfz5
    syl2anc
    mpbird
    cS
    cT
    vf
    vk
    cK
    cN
    birthday.s
    birthday.t
    birthdaylem2
    syl2anc
    @39
    @46
    @10
    cle
    wbr
    #
    @47
    @11
    cle
    wbr
    #
    @39
    @46
    @41
    @43
    cneg
    #
    vk
    csu
    #
    @10
    cle
    @39
    @41
    @45
    @56
    vk
    @39
    cc0
    @40
    fzfid
    #
    @39
    @42
    @41
    wcel
    #
    wa
    #
    @44
    @60
    @43
    c1
    clt
    wbr
    #
    @44
    crp
    wcel
    #
    @60
    @61
    @42
    cN
    c1
    cmul
    co
    #
    clt
    wbr
    #
    @60
    @42
    cN
    @63
    clt
    @60
    @42
    @40
    cN
    @60
    @42
    @59
    @42
    cn0
    wcel
    @39
    @42
    @40
    elfznn0
    adantl
    nn0red
    #
    @39
    @40
    cr
    wcel
    #
    @59
    @39
    @25
    @66
    @39
    cK
    @53
    nn0red
    #
    cK
    peano2rem
    syl
    #
    adantr
    @60
    cN
    @39
    @1
    @59
    @49
    adantr
    #
    nnred
    #
    @59
    @42
    @40
    cle
    wbr
    @39
    @42
    cc0
    @40
    elfzle2
    adantl
    @39
    @40
    cN
    clt
    wbr
    @59
    @39
    @40
    cK
    cN
    @68
    @67
    @39
    cN
    @49
    nnred
    @39
    cK
    @67
    ltm1d
    @50
    ltletrd
    adantr
    lelttrd
    @60
    cN
    @60
    cN
    @69
    nncnd
    mulid1d
    breqtrrd
    @60
    @42
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    @26
    cc0
    cN
    clt
    wbr
    #
    @61
    @64
    wb
    @65
    @60
    1red
    @70
    @60
    cN
    @69
    nngt0d
    #
    @42
    c1
    cN
    ltdivmul
    syl112anc
    mpbird
    #
    @60
    @43
    cr
    wcel
    #
    @72
    @61
    @62
    wb
    @60
    @42
    cN
    @65
    @69
    nndivred
    #
    1re
    @43
    c1
    difrp
    sylancl
    mpbid
    #
    relogcld
    #
    @60
    @43
    @77
    renegcld
    #
    @60
    @45
    @56
    cle
    wbr
    #
    @45
    ce
    cfv
    #
    @56
    ce
    cfv
    #
    cle
    wbr
    #
    @60
    @44
    c1
    @43
    ce
    cfv
    #
    cdiv
    co
    #
    @82
    @83
    cle
    @60
    @85
    c1
    @44
    cdiv
    co
    cle
    wbr
    #
    @44
    @86
    cle
    wbr
    #
    @60
    @43
    @77
    @60
    @71
    cc0
    @42
    cle
    wbr
    #
    @26
    @73
    cc0
    @43
    cle
    wbr
    @65
    @59
    @89
    @39
    @42
    cc0
    @40
    elfzle1
    adantl
    @70
    @74
    @42
    cN
    divge0
    syl22anc
    @75
    eflegeo
    @60
    @85
    cr
    wcel
    cc0
    @85
    clt
    wbr
    #
    @44
    cr
    wcel
    cc0
    @44
    clt
    wbr
    wa
    @87
    @88
    wb
    @60
    @43
    @77
    reefcld
    @60
    @76
    @90
    @77
    @43
    efgt0
    syl
    @60
    @44
    @78
    rpregt0d
    @85
    @44
    lerec2
    syl21anc
    mpbid
    @60
    @44
    @78
    reeflogd
    @60
    @43
    cc
    wcel
    @83
    @86
    wceq
    @60
    @43
    @77
    recnd
    #
    @43
    efneg
    syl
    3brtr4d
    @60
    @45
    cr
    wcel
    @56
    cr
    wcel
    @81
    @84
    wb
    @79
    @80
    @45
    @56
    efle
    syl2anc
    mpbird
    fsumle
    @39
    @57
    @41
    @43
    vk
    csu
    #
    cneg
    @10
    @39
    @41
    @43
    vk
    @58
    @91
    fsumneg
    @39
    @92
    @9
    @39
    @41
    @42
    vk
    csu
    #
    cN
    cdiv
    co
    @92
    @9
    @39
    @41
    @42
    cN
    vk
    @58
    @39
    cN
    @49
    nncnd
    @60
    @42
    @65
    recnd
    @1
    cN
    cc0
    wne
    @0
    @24
    cN
    nnne0
    ad2antlr
    fsumdivc
    @39
    @93
    @8
    cN
    cdiv
    @39
    @0
    @93
    @8
    wceq
    @53
    vk
    cK
    arisum2
    syl
    oveq1d
    eqtr3d
    negeqd
    eqtrd
    breqtrd
    @39
    @46
    cr
    wcel
    @36
    @54
    @55
    wb
    @39
    @41
    @45
    vk
    @58
    @79
    fsumrecl
    @2
    @36
    @24
    @38
    adantr
    @46
    @10
    efle
    syl2anc
    mpbid
    eqbrtrd
    @1
    @26
    @0
    @28
    adantl
    @37
    ltlecasei
end
