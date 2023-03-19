include "c1.mm"
include "cv.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cvma.mm"
include "cdiv.mm"
include "csu.mm"
include "clog.mm"
include "cmin.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "cpnf.mm"
include "cico.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "wtru.mm"
include "caddc.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "1re.mm"
include "elicopnf.mm"
include "mp1i.mm"
include "simprbda.mm"
include "1rp.mm"
include "a1i.mm"
include "simplbda.mm"
include "rpgecld.mm"
include "ex.mm"
include "ssrdv.mm"
include "rpssre.mm"
include "syl6ss.mm"
include "fzfid.mm"
include "cn.mm"
include "elfznn.mm"
include "adantl.mm"
include "vmacl.mm"
include "syl.mm"
include "nndivred.mm"
include "fsumrecl.mm"
include "relogcld.mm"
include "resubcld.mm"
include "recnd.mm"
include "cmpt.mm"
include "co1.mm"
include "vmadivsum.mm"
include "o1res2.mm"
include "simprl.mm"
include "simprr.mm"
include "readdcld.mm"
include "clt.mm"
include "adantr.mm"
include "abscld.mm"
include "ad2ant2r.mm"
include "abs2dif2d.mm"
include "cc0.mm"
include "nnrpd.mm"
include "vmage0.mm"
include "divge0d.mm"
include "fsumge0.mm"
include "absidd.mm"
include "logge0d.mm"
include "oveq12d.mm"
include "breqtrd.mm"
include "cuz.mm"
include "wss.mm"
include "simprll.mm"
include "ltled.mm"
include "flword2.mm"
include "syl3anc.mm"
include "fzss2.mm"
include "fsumless.mm"
include "logled.mm"
include "mpbid.mm"
include "le2addd.mm"
include "letrd.mm"
include "o1bddrp.mm"
include "trud.mm"

theorem vmadivsumb
  let vx: setvar x
  let vn: setvar n
  let vc: setvar c
  let vy: setvar y

  disjoint c n
  disjoint c x
  disjoint n x
  disjoint c y
  disjoint n y
  disjoint x y
  assert |- E. c e. RR+ A. x e. ( 1 [,) +oo ) ( abs ` ( sum_ n e. ( 1 ... ( |_ ` x ) ) ( ( Lam ` n ) / n ) - ( log ` x ) ) ) <_ c

  proof
    c1
    vx
    cv
    #
    cfl
    cfv
    #
    cfz
    co
    #
    vn
    cv
    #
    cvma
    cfv
    #
    @3
    cdiv
    co
    #
    vn
    csu
    #
    @0
    clog
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    vc
    cv
    cle
    wbr
    vx
    c1
    cpnf
    cico
    co
    #
    wral
    vc
    crp
    wrex
    wtru
    vx
    vy
    @10
    @8
    c1
    vc
    c1
    vy
    cv
    #
    cfl
    cfv
    #
    cfz
    co
    #
    @5
    vn
    csu
    #
    @11
    clog
    cfv
    #
    caddc
    co
    #
    wtru
    @10
    crp
    cr
    wtru
    vx
    @10
    crp
    wtru
    @0
    @10
    wcel
    #
    @0
    crp
    wcel
    #
    wtru
    @17
    wa
    #
    @0
    c1
    wtru
    @17
    @0
    cr
    wcel
    #
    c1
    @0
    cle
    wbr
    #
    c1
    cr
    wcel
    #
    @17
    @20
    @21
    wa
    wb
    wtru
    1re
    c1
    @0
    elicopnf
    mp1i
    #
    simprbda
    #
    c1
    crp
    wcel
    #
    @19
    1rp
    a1i
    wtru
    @17
    @20
    @21
    @23
    simplbda
    #
    rpgecld
    #
    ex
    ssrdv
    #
    rpssre
    syl6ss
    @22
    wtru
    1re
    a1i
    @19
    @8
    @19
    @6
    @7
    @19
    @2
    @5
    vn
    @19
    c1
    @1
    fzfid
    #
    @19
    @3
    @2
    wcel
    #
    wa
    #
    @4
    @3
    @31
    @3
    cn
    wcel
    #
    @4
    cr
    wcel
    #
    @30
    @32
    @19
    @3
    @1
    elfznn
    adantl
    #
    @3
    vmacl
    #
    syl
    #
    @34
    nndivred
    #
    fsumrecl
    #
    @19
    @0
    @27
    relogcld
    #
    resubcld
    #
    recnd
    wtru
    vx
    @10
    crp
    @8
    @28
    vx
    crp
    @8
    cmpt
    co1
    wcel
    wtru
    vx
    vn
    vmadivsum
    a1i
    o1res2
    wtru
    @11
    cr
    wcel
    #
    c1
    @11
    cle
    wbr
    #
    wa
    #
    wa
    #
    @14
    @15
    @44
    @13
    @5
    vn
    @44
    c1
    @12
    fzfid
    @44
    @3
    @13
    wcel
    #
    wa
    #
    @4
    @3
    @46
    @32
    @33
    @45
    @32
    @44
    @3
    @12
    elfznn
    #
    adantl
    #
    @35
    syl
    @48
    nndivred
    fsumrecl
    #
    @44
    @11
    @44
    @11
    c1
    wtru
    @41
    @42
    simprl
    @25
    @44
    1rp
    a1i
    wtru
    @41
    @42
    simprr
    rpgecld
    #
    relogcld
    readdcld
    #
    @19
    @43
    @0
    @11
    clt
    wbr
    #
    wa
    #
    wa
    #
    @9
    @6
    @7
    caddc
    co
    #
    @16
    @54
    @8
    @54
    @8
    @19
    @8
    cr
    wcel
    @53
    @40
    adantr
    recnd
    abscld
    @54
    @6
    @7
    @19
    @6
    cr
    wcel
    @53
    @38
    adantr
    #
    @54
    @0
    @19
    @18
    @53
    @27
    adantr
    #
    relogcld
    #
    readdcld
    wtru
    @43
    @16
    cr
    wcel
    @17
    @52
    @51
    ad2ant2r
    @54
    @9
    @6
    cabs
    cfv
    #
    @7
    cabs
    cfv
    #
    caddc
    co
    @55
    cle
    @54
    @6
    @7
    @54
    @6
    @56
    recnd
    @54
    @7
    @58
    recnd
    abs2dif2d
    @54
    @59
    @6
    @60
    @7
    caddc
    @54
    @6
    @56
    @19
    cc0
    @6
    cle
    wbr
    @53
    @19
    @2
    @5
    vn
    @29
    @37
    @31
    @4
    @3
    @36
    @31
    @3
    @34
    nnrpd
    @31
    @32
    cc0
    @4
    cle
    wbr
    #
    @34
    @3
    vmage0
    #
    syl
    divge0d
    fsumge0
    adantr
    absidd
    @54
    @7
    @19
    @7
    cr
    wcel
    @53
    @39
    adantr
    @54
    @0
    @19
    @20
    @53
    @24
    adantr
    #
    @19
    @21
    @53
    @26
    adantr
    logge0d
    absidd
    oveq12d
    breqtrd
    @54
    @6
    @7
    @14
    @15
    @56
    @58
    wtru
    @43
    @14
    cr
    wcel
    @17
    @52
    @49
    ad2ant2r
    @54
    @11
    wtru
    @43
    @11
    crp
    wcel
    @17
    @52
    @50
    ad2ant2r
    relogcld
    @54
    @13
    @5
    @2
    vn
    @54
    c1
    @12
    fzfid
    @54
    @45
    wa
    #
    @4
    @3
    @64
    @32
    @33
    @45
    @32
    @54
    @47
    adantl
    #
    @35
    syl
    #
    @65
    nndivred
    @64
    @4
    @3
    @66
    @64
    @3
    @65
    nnrpd
    @64
    @32
    @61
    @65
    @62
    syl
    divge0d
    @54
    @12
    @1
    cuz
    cfv
    wcel
    #
    @2
    @13
    wss
    @54
    @20
    @41
    @0
    @11
    cle
    wbr
    #
    @67
    @63
    @19
    @41
    @42
    @52
    simprll
    #
    @54
    @0
    @11
    @63
    @69
    @19
    @43
    @52
    simprr
    ltled
    #
    @0
    @11
    flword2
    syl3anc
    @1
    c1
    @12
    fzss2
    syl
    fsumless
    @54
    @68
    @7
    @15
    cle
    wbr
    @70
    @54
    @0
    @11
    @57
    @54
    @11
    @0
    @69
    @57
    @70
    rpgecld
    logled
    mpbid
    le2addd
    letrd
    o1bddrp
    trud
end
