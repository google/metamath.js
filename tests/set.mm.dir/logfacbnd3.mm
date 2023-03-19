include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cfl.mm"
include "cfv.mm"
include "cfa.mm"
include "clog.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "cabs.mm"
include "caddc.mm"
include "cr.mm"
include "cn0.mm"
include "cn.mm"
include "cc0.mm"
include "simpl.mm"
include "rprege0d.mm"
include "flge0nn0.mm"
include "syl.mm"
include "faccl.mm"
include "nnrpd.mm"
include "relogcl.mm"
include "rpre.mm"
include "adantr.mm"
include "peano2rem.mm"
include "remulcld.mm"
include "resubcld.mm"
include "recnd.mm"
include "abscld.mm"
include "cc.mm"
include "ax-1cn.mm"
include "subcl.mm"
include "sylancl.mm"
include "abs1.mm"
include "oveq2i.mm"
include "abs2dif.mm"
include "syl5eqbrr.mm"
include "cv.mm"
include "cfz.mm"
include "csu.mm"
include "cmpt.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "sumeq1d.mm"
include "id.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt3i.mm"
include "logfac.mm"
include "eqtr4d.mm"
include "1rp.mm"
include "cz.mm"
include "1z.mm"
include "flid.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "0cn.mm"
include "log1.mm"
include "fsum1.mm"
include "mp2an.mm"
include "subcli.mm"
include "mulid2i.mm"
include "nncan.mm"
include "mp1i.mm"
include "fveq2d.mm"
include "cpnf.mm"
include "cioo.mm"
include "ioorp.mm"
include "eqcomi.mm"
include "nnuz.mm"
include "a1i.mm"
include "1re.mm"
include "cxr.mm"
include "pnfxr.mm"
include "1nn0.mm"
include "nn0addge1i.mm"
include "0red.mm"
include "adantl.mm"
include "nnrp.mm"
include "sylan2.mm"
include "cdv.mm"
include "advlog.mm"
include "w3a.mm"
include "simp32.mm"
include "wb.mm"
include "logleb.mm"
include "3ad2ant2.mm"
include "mpbid.mm"
include "simprr.mm"
include "simprl.mm"
include "sylancr.mm"
include "1le1.mm"
include "simpr.mm"
include "rexrd.mm"
include "pnfge.mm"
include "dvfsum2.mm"
include "eqbrtrrd.mm"
include "letrd.mm"
include "lesubaddd.mm"

theorem logfacbnd3
  let cA: class A
  let vn: setvar n
  let vx: setvar x
  let vk: setvar k
  let vy: setvar y
  let cN: class N


  assert |- ( ( A e. RR+ /\ 1 <_ A ) -> ( abs ` ( ( log ` ( ! ` ( |_ ` A ) ) ) - ( A x. ( ( log ` A ) - 1 ) ) ) ) <_ ( ( log ` A ) + 1 ) )

  proof
    cA
    crp
    wcel
    #
    c1
    cA
    cle
    wbr
    #
    wa
    #
    cA
    cfl
    cfv
    #
    cfa
    cfv
    #
    clog
    cfv
    #
    cA
    cA
    clog
    cfv
    #
    c1
    cmin
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    c1
    cmin
    co
    #
    @6
    cle
    wbr
    @10
    @6
    c1
    caddc
    co
    cle
    wbr
    @2
    @11
    @9
    c1
    cmin
    co
    #
    cabs
    cfv
    #
    @6
    @2
    @10
    cr
    wcel
    @11
    cr
    wcel
    @2
    @9
    @2
    @9
    @2
    @5
    @8
    @2
    @4
    crp
    wcel
    @5
    cr
    wcel
    @2
    @4
    @2
    @3
    cn0
    wcel
    #
    @4
    cn
    wcel
    @2
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    wa
    @14
    @2
    cA
    @0
    @1
    simpl
    #
    rprege0d
    cA
    flge0nn0
    syl
    #
    @3
    faccl
    syl
    nnrpd
    @4
    relogcl
    syl
    @2
    cA
    @7
    @0
    @15
    @1
    cA
    rpre
    adantr
    #
    @2
    @6
    cr
    wcel
    #
    @7
    cr
    wcel
    @0
    @19
    @1
    cA
    relogcl
    adantr
    #
    @6
    peano2rem
    syl
    remulcld
    resubcld
    recnd
    #
    abscld
    #
    @10
    peano2rem
    syl
    @2
    @12
    @2
    @9
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @12
    cc
    wcel
    @21
    ax-1cn
    @9
    c1
    subcl
    sylancl
    abscld
    @20
    @2
    @11
    @10
    c1
    cabs
    cfv
    #
    cmin
    co
    #
    @13
    cle
    @25
    c1
    @10
    cmin
    abs1
    oveq2i
    @2
    @23
    @24
    @26
    @13
    cle
    wbr
    @21
    ax-1cn
    @9
    c1
    abs2dif
    sylancl
    syl5eqbrr
    @2
    cA
    vx
    crp
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
    clog
    cfv
    #
    vn
    csu
    #
    @27
    @27
    clog
    cfv
    #
    c1
    cmin
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cmpt
    #
    cfv
    #
    c1
    @37
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    @13
    @6
    cle
    @2
    @40
    @12
    cabs
    @2
    @38
    @9
    @39
    c1
    cmin
    @2
    @38
    c1
    @3
    cfz
    co
    #
    @31
    vn
    csu
    #
    @8
    cmin
    co
    #
    @9
    @0
    @38
    @43
    wceq
    @1
    vx
    cA
    @36
    @43
    crp
    @37
    @27
    cA
    wceq
    #
    @32
    @42
    @35
    @8
    cmin
    @44
    @29
    @41
    @31
    vn
    @44
    @28
    @3
    c1
    cfz
    @27
    cA
    cfl
    fveq2
    oveq2d
    sumeq1d
    @44
    @27
    cA
    @34
    @7
    cmul
    @44
    id
    @44
    @33
    @6
    c1
    cmin
    @27
    cA
    clog
    fveq2
    #
    oveq1d
    oveq12d
    oveq12d
    @37
    eqid
    #
    @32
    @35
    cmin
    ovex
    #
    fvmpt3i
    adantr
    @2
    @5
    @42
    @8
    cmin
    @2
    @14
    @5
    @42
    wceq
    @17
    vn
    @3
    logfac
    syl
    oveq1d
    eqtr4d
    c1
    crp
    wcel
    #
    @39
    c1
    wceq
    @2
    1rp
    vx
    c1
    @36
    c1
    crp
    @37
    @27
    c1
    wceq
    #
    @36
    cc0
    cc0
    c1
    cmin
    co
    #
    cmin
    co
    #
    c1
    @49
    @32
    cc0
    @35
    @50
    cmin
    @49
    @32
    c1
    c1
    cfz
    co
    #
    @31
    vn
    csu
    #
    cc0
    @49
    @29
    @52
    @31
    vn
    @49
    @28
    c1
    c1
    cfz
    @49
    @28
    c1
    cfl
    cfv
    #
    c1
    @27
    c1
    cfl
    fveq2
    c1
    cz
    wcel
    #
    @54
    c1
    wceq
    1z
    c1
    flid
    ax-mp
    syl6eq
    oveq2d
    sumeq1d
    @55
    cc0
    cc
    wcel
    #
    @53
    cc0
    wceq
    1z
    0cn
    @31
    cc0
    vn
    c1
    @30
    c1
    wceq
    @31
    c1
    clog
    cfv
    #
    cc0
    @30
    c1
    clog
    fveq2
    log1
    syl6eq
    fsum1
    mp2an
    syl6eq
    @49
    @35
    c1
    @50
    cmul
    co
    @50
    @49
    @27
    c1
    @34
    @50
    cmul
    @49
    id
    @49
    @33
    cc0
    c1
    cmin
    @49
    @33
    @57
    cc0
    @27
    c1
    clog
    fveq2
    log1
    syl6eq
    oveq1d
    oveq12d
    @50
    cc0
    c1
    0cn
    ax-1cn
    subcli
    mulid2i
    syl6eq
    oveq12d
    @56
    @24
    @51
    c1
    wceq
    0cn
    ax-1cn
    cc0
    c1
    nncan
    mp2an
    syl6eq
    @46
    @47
    fvmpt3i
    mp1i
    oveq12d
    fveq2d
    @2
    vx
    @35
    @33
    @31
    c1
    crp
    cc0
    cpnf
    vn
    @6
    @37
    c1
    cr
    c1
    cA
    cn
    cc0
    cpnf
    cioo
    co
    crp
    ioorp
    eqcomi
    nnuz
    @55
    @2
    1z
    a1i
    c1
    cr
    wcel
    @2
    1re
    a1i
    #
    cpnf
    cxr
    wcel
    @2
    pnfxr
    a1i
    c1
    c1
    c1
    caddc
    co
    cle
    wbr
    @2
    c1
    c1
    1re
    1nn0
    nn0addge1i
    a1i
    @2
    0red
    @2
    @27
    crp
    wcel
    #
    wa
    #
    @27
    @34
    @59
    @27
    cr
    wcel
    @2
    @27
    rpre
    adantl
    @60
    @33
    cr
    wcel
    #
    @34
    cr
    wcel
    @59
    @61
    @2
    @27
    relogcl
    adantl
    #
    @33
    peano2rem
    syl
    remulcld
    @62
    @27
    cn
    wcel
    @2
    @59
    @61
    @27
    nnrp
    @62
    sylan2
    cr
    vx
    crp
    @35
    cmpt
    cdv
    co
    vx
    crp
    @33
    cmpt
    wceq
    @2
    vx
    advlog
    a1i
    @27
    @30
    clog
    fveq2
    @2
    @59
    @30
    crp
    wcel
    wa
    #
    c1
    @27
    cle
    wbr
    #
    @27
    @30
    cle
    wbr
    #
    @30
    cpnf
    cle
    wbr
    #
    w3a
    #
    w3a
    @65
    @33
    @31
    cle
    wbr
    #
    @2
    @63
    @64
    @65
    @66
    simp32
    @63
    @2
    @65
    @68
    wb
    @67
    @27
    @30
    logleb
    3ad2ant2
    mpbid
    @46
    @2
    @59
    @64
    wa
    wa
    #
    cc0
    @57
    @33
    cle
    log1
    @69
    @64
    @57
    @33
    cle
    wbr
    #
    @2
    @59
    @64
    simprr
    @69
    @48
    @59
    @64
    @70
    wb
    1rp
    @2
    @59
    @64
    simprl
    c1
    @27
    logleb
    sylancr
    mpbid
    syl5eqbrr
    @48
    @2
    1rp
    a1i
    @16
    c1
    c1
    cle
    wbr
    @2
    1le1
    a1i
    @0
    @1
    simpr
    @2
    cA
    cxr
    wcel
    cA
    cpnf
    cle
    wbr
    @2
    cA
    @18
    rexrd
    cA
    pnfge
    syl
    @45
    dvfsum2
    eqbrtrrd
    letrd
    @2
    @10
    c1
    @6
    @22
    @58
    @20
    lesubaddd
    mpbid
end
