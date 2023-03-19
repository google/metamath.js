include "wcel.mm"
include "caddc.mm"
include "cn.mm"
include "c1.mm"
include "cneg.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cexp.mm"
include "cdiv.mm"
include "cmul.mm"
include "cmpt.mm"
include "cseq.mm"
include "clog.mm"
include "cfv.mm"
include "cli.mm"
include "nnuz.mm"
include "1zzd.mm"
include "cc.mm"
include "neg1cn.mm"
include "a1i.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "ax-1cn.mm"
include "ccom.mm"
include "cbl.mm"
include "wa.mm"
include "eleq2i.mm"
include "cxmt.mm"
include "cxr.mm"
include "wb.mm"
include "cnxmet.mm"
include "crp.mm"
include "1rp.mm"
include "rpxr.mm"
include "ax-mp.mm"
include "elbl.mm"
include "mp3an.mm"
include "bitri.mm"
include "simplbi.mm"
include "subcl.mm"
include "sylancr.mm"
include "wceq.mm"
include "eqid.mm"
include "cnmetdval.mm"
include "simprbi.mm"
include "eqbrtrrd.mm"
include "logtayl.mm"
include "syl2anc.mm"
include "nncan.mm"
include "fveq2d.mm"
include "negeqd.mm"
include "breqtrd.mm"
include "oveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "cn0.mm"
include "nnnn0.mm"
include "expcl.mm"
include "syl2an.mm"
include "nncn.mm"
include "cc0.mm"
include "wne.mm"
include "nnne0.mm"
include "divcld.mm"
include "eqeltrd.mm"
include "divnegd.mm"
include "mulm1d.mm"
include "sylancl.mm"
include "mulneg1d.mm"
include "neg1ne0.mm"
include "cz.mm"
include "nnz.mm"
include "expm1d.mm"
include "ax-1ne0.mm"
include "divneg2d.mm"
include "div1d.mm"
include "3eqtr2d.mm"
include "oveq1d.mm"
include "negsubdi2.mm"
include "eqtr2d.mm"
include "adantr.mm"
include "mulexp.mm"
include "mp3an1.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"
include "nnm1nn0.mm"
include "div23d.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "isermulc2.mm"
include "cmnf.mm"
include "cioc.mm"
include "cdif.mm"
include "dvlog2lem.mm"
include "sseli.mm"
include "logdmn0.mm"
include "syl.mm"
include "logcld.mm"
include "negcld.mm"
include "negnegd.mm"

theorem logtayl2
  let cA: class A
  let cS: class S
  let vk: setvar k
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume logtayl2.s: |- S = ( 1 ( ball ` ( abs o. - ) ) 1 )

  disjoint A k
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j r
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint A j
  disjoint k m
  disjoint k n
  disjoint k r
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint m n
  disjoint m r
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint S n
  assert |- ( A e. S -> seq 1 ( + , ( k e. NN |-> ( ( ( -u 1 ^ ( k - 1 ) ) / k ) x. ( ( A - 1 ) ^ k ) ) ) ) ~~> ( log ` A ) )

  proof
    cA
    cS
    wcel
    #
    caddc
    vk
    cn
    c1
    cneg
    #
    vk
    cv
    #
    c1
    cmin
    co
    #
    cexp
    co
    #
    @2
    cdiv
    co
    #
    cA
    c1
    cmin
    co
    #
    @2
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    c1
    cseq
    @1
    cA
    clog
    cfv
    #
    cneg
    #
    cmul
    co
    #
    @10
    cli
    @0
    @11
    @1
    vn
    vk
    cn
    c1
    cA
    cmin
    co
    #
    @2
    cexp
    co
    #
    @2
    cdiv
    co
    #
    cmpt
    #
    @9
    c1
    cn
    nnuz
    @0
    1zzd
    @1
    cc
    wcel
    #
    @0
    neg1cn
    a1i
    @0
    caddc
    @16
    c1
    cseq
    #
    c1
    @13
    cmin
    co
    #
    clog
    cfv
    #
    cneg
    #
    @11
    cli
    @0
    @13
    cc
    wcel
    #
    @13
    cabs
    cfv
    #
    c1
    clt
    wbr
    @18
    @21
    cli
    wbr
    @0
    c1
    cc
    wcel
    #
    cA
    cc
    wcel
    #
    @22
    ax-1cn
    @0
    @25
    c1
    cA
    cabs
    cmin
    ccom
    #
    co
    #
    c1
    clt
    wbr
    #
    @0
    cA
    c1
    c1
    @26
    cbl
    cfv
    co
    #
    wcel
    #
    @25
    @28
    wa
    #
    cS
    @29
    cA
    logtayl2.s
    eleq2i
    @26
    cc
    cxmt
    cfv
    wcel
    @24
    c1
    cxr
    wcel
    #
    @30
    @31
    wb
    cnxmet
    ax-1cn
    c1
    crp
    wcel
    @32
    1rp
    c1
    rpxr
    ax-mp
    cA
    @26
    c1
    c1
    cc
    elbl
    mp3an
    bitri
    #
    simplbi
    #
    c1
    cA
    subcl
    sylancr
    #
    @0
    @27
    @23
    c1
    clt
    @0
    @24
    @25
    @27
    @23
    wceq
    ax-1cn
    @34
    c1
    cA
    @26
    @26
    eqid
    cnmetdval
    sylancr
    @0
    @25
    @28
    @33
    simprbi
    eqbrtrrd
    @13
    vk
    logtayl
    syl2anc
    @0
    @20
    @10
    @0
    @19
    cA
    clog
    @0
    @24
    @25
    @19
    cA
    wceq
    ax-1cn
    @34
    c1
    cA
    nncan
    sylancr
    fveq2d
    negeqd
    breqtrd
    @0
    vn
    cv
    #
    cn
    wcel
    #
    wa
    #
    @36
    @16
    cfv
    #
    @13
    @36
    cexp
    co
    #
    @36
    cdiv
    co
    #
    cc
    @37
    @39
    @41
    wceq
    @0
    vk
    @36
    @15
    @41
    cn
    @16
    @2
    @36
    wceq
    #
    @14
    @40
    @2
    @36
    cdiv
    @2
    @36
    @13
    cexp
    oveq2
    @42
    id
    #
    oveq12d
    @16
    eqid
    @40
    @36
    cdiv
    ovex
    fvmpt
    adantl
    #
    @38
    @40
    @36
    @0
    @22
    @36
    cn0
    wcel
    #
    @40
    cc
    wcel
    @37
    @35
    @36
    nnnn0
    #
    @13
    @36
    expcl
    syl2an
    #
    @37
    @36
    cc
    wcel
    @0
    @36
    nncn
    adantl
    #
    @37
    @36
    cc0
    wne
    @0
    @36
    nnne0
    adantl
    #
    divcld
    #
    eqeltrd
    @38
    @1
    @36
    c1
    cmin
    co
    #
    cexp
    co
    #
    @36
    cdiv
    co
    #
    @6
    @36
    cexp
    co
    #
    cmul
    co
    #
    @1
    @41
    cmul
    co
    #
    @36
    @9
    cfv
    #
    @1
    @39
    cmul
    co
    @38
    @56
    @52
    @54
    cmul
    co
    #
    @36
    cdiv
    co
    #
    @55
    @38
    @41
    cneg
    @40
    cneg
    #
    @36
    cdiv
    co
    @56
    @59
    @38
    @40
    @36
    @47
    @48
    @49
    divnegd
    @38
    @41
    @50
    mulm1d
    @38
    @58
    @60
    @36
    cdiv
    @38
    @1
    @36
    cexp
    co
    #
    cneg
    #
    @54
    cmul
    co
    @61
    @54
    cmul
    co
    #
    cneg
    @58
    @60
    @38
    @61
    @54
    @38
    @17
    @45
    @61
    cc
    wcel
    neg1cn
    @37
    @45
    @0
    @46
    adantl
    @1
    @36
    expcl
    sylancr
    #
    @0
    @6
    cc
    wcel
    #
    @45
    @54
    cc
    wcel
    @37
    @0
    @25
    @24
    @65
    @34
    ax-1cn
    cA
    c1
    subcl
    sylancl
    #
    @46
    @6
    @36
    expcl
    syl2an
    #
    mulneg1d
    @38
    @52
    @62
    @54
    cmul
    @38
    @52
    @61
    @1
    cdiv
    co
    @61
    c1
    cdiv
    co
    #
    cneg
    @62
    @38
    @1
    @36
    @17
    @38
    neg1cn
    a1i
    @1
    cc0
    wne
    @38
    neg1ne0
    a1i
    @37
    @36
    cz
    wcel
    @0
    @36
    nnz
    adantl
    expm1d
    @38
    @61
    c1
    @64
    @24
    @38
    ax-1cn
    a1i
    c1
    cc0
    wne
    @38
    ax-1ne0
    a1i
    divneg2d
    @38
    @68
    @61
    @38
    @61
    @64
    div1d
    negeqd
    3eqtr2d
    oveq1d
    @38
    @40
    @63
    @38
    @40
    @1
    @6
    cmul
    co
    #
    @36
    cexp
    co
    #
    @63
    @0
    @40
    @70
    wceq
    @37
    @0
    @13
    @69
    @36
    cexp
    @0
    @69
    @6
    cneg
    #
    @13
    @0
    @6
    @66
    mulm1d
    @0
    @25
    @24
    @71
    @13
    wceq
    @34
    ax-1cn
    cA
    c1
    negsubdi2
    sylancl
    eqtr2d
    oveq1d
    adantr
    @0
    @65
    @45
    @70
    @63
    wceq
    #
    @37
    @66
    @46
    @17
    @65
    @45
    @72
    neg1cn
    @1
    @6
    @36
    mulexp
    mp3an1
    syl2an
    eqtrd
    negeqd
    3eqtr4d
    oveq1d
    3eqtr4d
    @38
    @52
    @54
    @36
    @38
    @17
    @51
    cn0
    wcel
    #
    @52
    cc
    wcel
    neg1cn
    @37
    @73
    @0
    @36
    nnm1nn0
    adantl
    @1
    @51
    expcl
    sylancr
    @67
    @48
    @49
    div23d
    eqtr2d
    @37
    @57
    @55
    wceq
    @0
    vk
    @36
    @8
    @55
    cn
    @9
    @42
    @5
    @53
    @7
    @54
    cmul
    @42
    @4
    @52
    @2
    @36
    cdiv
    @42
    @3
    @51
    @1
    cexp
    @2
    @36
    c1
    cmin
    oveq1
    oveq2d
    @43
    oveq12d
    @2
    @36
    @6
    cexp
    oveq2
    oveq12d
    @9
    eqid
    @53
    @54
    cmul
    ovex
    fvmpt
    adantl
    @38
    @39
    @41
    @1
    cmul
    @44
    oveq2d
    3eqtr4d
    isermulc2
    @0
    @12
    @11
    cneg
    @10
    @0
    @11
    @0
    @10
    @0
    cA
    @34
    @0
    cA
    cc
    cmnf
    cc0
    cioc
    co
    cdif
    #
    wcel
    cA
    cc0
    wne
    cS
    @74
    cA
    cS
    logtayl2.s
    dvlog2lem
    sseli
    cA
    @74
    @74
    eqid
    logdmn0
    syl
    logcld
    #
    negcld
    mulm1d
    @0
    @10
    @75
    negnegd
    eqtrd
    breqtrd
end
