include "cprime.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "cmo.mm"
include "wceq.mm"
include "cdvds.mm"
include "wbr.mm"
include "caddc.mm"
include "wo.mm"
include "cmul.mm"
include "cc0.mm"
include "cz.mm"
include "elfzelz.mm"
include "adantl.mm"
include "peano2zm.mm"
include "syl.mm"
include "zcnd.mm"
include "peano2zd.mm"
include "mulcomd.mm"
include "cc.mm"
include "ax-1cn.mm"
include "subsq.mm"
include "sylancl.mm"
include "sqvald.mm"
include "sq1.mm"
include "a1i.mm"
include "oveq12d.mm"
include "3eqtr2d.mm"
include "breq2d.mm"
include "1e0p1.mm"
include "oveq1i.mm"
include "wss.mm"
include "0z.mm"
include "fzp1ss.mm"
include "ax-mp.mm"
include "eqsstri.mm"
include "simpr.mm"
include "sseldi.mm"
include "biantrurd.mm"
include "bitrd.mm"
include "wb.mm"
include "simpl.mm"
include "euclemma.mm"
include "syl3anc.mm"
include "wn.mm"
include "cn.mm"
include "prmnn.mm"
include "fzm1ndvds.mm"
include "sylan.mm"
include "eqid.mm"
include "prmdiveq.mm"
include "3bitr3rd.mm"
include "1zzd.mm"
include "moddvds.mm"
include "cr.mm"
include "crp.mm"
include "cle.mm"
include "clt.mm"
include "elfznn.mm"
include "nnred.mm"
include "nnrpd.mm"
include "nnnn0d.mm"
include "nn0ge0d.mm"
include "elfzle2.mm"
include "prmz.mm"
include "zltlem1.mm"
include "syl2anr.mm"
include "mpbird.mm"
include "modid.mm"
include "syl22anc.mm"
include "cuz.mm"
include "cfv.mm"
include "prmuz2.mm"
include "eluz2b2.mm"
include "simprbi.mm"
include "1mod.mm"
include "syl2anc.mm"
include "eqeq12d.mm"
include "bitr3d.mm"
include "cneg.mm"
include "znegcld.mm"
include "nncnd.mm"
include "mulid2d.mm"
include "oveq2d.mm"
include "neg1cn.mm"
include "addcom.mm"
include "sylancr.mm"
include "negsub.mm"
include "3eqtrd.mm"
include "oveq1d.mm"
include "neg1rr.mm"
include "modcyc.mm"
include "peano2rem.mm"
include "cn0.mm"
include "nnm1nn0.mm"
include "ltm1d.mm"
include "3eqtr3d.mm"
include "subneg.mm"
include "orbi12d.mm"

theorem wilthlem1
  let cP: class P
  let cN: class N


  assert |- ( ( P e. Prime /\ N e. ( 1 ... ( P - 1 ) ) ) -> ( N = ( ( N ^ ( P - 2 ) ) mod P ) <-> ( N = 1 \/ N = ( P - 1 ) ) ) )

  proof
    cP
    cprime
    wcel
    #
    cN
    c1
    cP
    c1
    cmin
    co
    #
    cfz
    co
    #
    wcel
    #
    wa
    #
    cN
    cN
    cP
    c2
    cmin
    co
    cexp
    co
    cP
    cmo
    co
    #
    wceq
    #
    cP
    cN
    c1
    cmin
    co
    #
    cdvds
    wbr
    #
    cP
    cN
    c1
    caddc
    co
    #
    cdvds
    wbr
    #
    wo
    #
    cN
    c1
    wceq
    #
    cN
    @1
    wceq
    #
    wo
    @4
    cP
    @7
    @9
    cmul
    co
    #
    cdvds
    wbr
    #
    cN
    cc0
    @1
    cfz
    co
    #
    wcel
    #
    cP
    cN
    cN
    cmul
    co
    #
    c1
    cmin
    co
    #
    cdvds
    wbr
    #
    wa
    #
    @11
    @6
    @4
    @15
    @20
    @21
    @4
    @14
    @19
    cP
    cdvds
    @4
    @14
    @9
    @7
    cmul
    co
    #
    cN
    c2
    cexp
    co
    #
    c1
    c2
    cexp
    co
    #
    cmin
    co
    #
    @19
    @4
    @7
    @9
    @4
    @7
    @4
    cN
    cz
    wcel
    #
    @7
    cz
    wcel
    #
    @3
    @26
    @0
    cN
    c1
    @1
    elfzelz
    #
    adantl
    #
    cN
    peano2zm
    syl
    #
    zcnd
    @4
    @9
    @4
    cN
    @29
    peano2zd
    #
    zcnd
    mulcomd
    @4
    cN
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @25
    @22
    wceq
    @4
    cN
    @29
    zcnd
    #
    ax-1cn
    cN
    c1
    subsq
    sylancl
    @4
    @23
    @18
    @24
    c1
    cmin
    @4
    cN
    @34
    sqvald
    @24
    c1
    wceq
    @4
    sq1
    a1i
    oveq12d
    3eqtr2d
    breq2d
    @4
    @17
    @20
    @4
    @2
    @16
    cN
    @2
    cc0
    c1
    caddc
    co
    #
    @1
    cfz
    co
    #
    @16
    c1
    @35
    @1
    cfz
    1e0p1
    oveq1i
    cc0
    cz
    wcel
    @36
    @16
    wss
    0z
    cc0
    @1
    fzp1ss
    ax-mp
    eqsstri
    @0
    @3
    simpr
    sseldi
    biantrurd
    bitrd
    @4
    @0
    @27
    @9
    cz
    wcel
    @15
    @11
    wb
    @0
    @3
    simpl
    #
    @30
    @31
    cP
    @7
    @9
    euclemma
    syl3anc
    @4
    @0
    @26
    cP
    cN
    cdvds
    wbr
    wn
    #
    @21
    @6
    wb
    @37
    @29
    @0
    cP
    cn
    wcel
    #
    @3
    @38
    cP
    prmnn
    #
    cP
    cN
    fzm1ndvds
    sylan
    cN
    cP
    @5
    cN
    @5
    eqid
    prmdiveq
    syl3anc
    3bitr3rd
    @4
    @8
    @12
    @10
    @13
    @4
    cN
    cP
    cmo
    co
    #
    c1
    cP
    cmo
    co
    #
    wceq
    #
    @8
    @12
    @4
    @39
    @26
    c1
    cz
    wcel
    #
    @43
    @8
    wb
    @4
    @0
    @39
    @37
    @40
    syl
    #
    @29
    @4
    1zzd
    #
    cN
    c1
    cP
    moddvds
    syl3anc
    @4
    @41
    cN
    @42
    c1
    @4
    cN
    cr
    wcel
    cP
    crp
    wcel
    #
    cc0
    cN
    cle
    wbr
    cN
    cP
    clt
    wbr
    #
    @41
    cN
    wceq
    @4
    cN
    @3
    cN
    cn
    wcel
    @0
    cN
    @1
    elfznn
    adantl
    #
    nnred
    @4
    cP
    @45
    nnrpd
    #
    @4
    cN
    @4
    cN
    @49
    nnnn0d
    nn0ge0d
    @4
    @48
    cN
    @1
    cle
    wbr
    #
    @3
    @51
    @0
    cN
    c1
    @1
    elfzle2
    adantl
    @3
    @26
    cP
    cz
    wcel
    @48
    @51
    wb
    @0
    @28
    cP
    prmz
    cN
    cP
    zltlem1
    syl2anr
    mpbird
    cN
    cP
    modid
    syl22anc
    #
    @4
    cP
    cr
    wcel
    #
    c1
    cP
    clt
    wbr
    #
    @42
    c1
    wceq
    @4
    cP
    @45
    nnred
    #
    @4
    cP
    c2
    cuz
    cfv
    wcel
    #
    @54
    @4
    @0
    @56
    @37
    cP
    prmuz2
    syl
    @56
    @39
    @54
    cP
    eluz2b2
    simprbi
    syl
    cP
    1mod
    syl2anc
    eqeq12d
    bitr3d
    @4
    @41
    c1
    cneg
    #
    cP
    cmo
    co
    #
    wceq
    #
    cP
    cN
    @57
    cmin
    co
    #
    cdvds
    wbr
    #
    @13
    @10
    @4
    @39
    @26
    @57
    cz
    wcel
    @59
    @61
    wb
    @45
    @29
    @4
    c1
    @46
    znegcld
    cN
    @57
    cP
    moddvds
    syl3anc
    @4
    @41
    cN
    @58
    @1
    @52
    @4
    @57
    c1
    cP
    cmul
    co
    #
    caddc
    co
    #
    cP
    cmo
    co
    #
    @1
    cP
    cmo
    co
    #
    @58
    @1
    @4
    @63
    @1
    cP
    cmo
    @4
    @63
    @57
    cP
    caddc
    co
    #
    cP
    @57
    caddc
    co
    #
    @1
    @4
    @62
    cP
    @57
    caddc
    @4
    cP
    @4
    cP
    @45
    nncnd
    #
    mulid2d
    oveq2d
    @4
    @57
    cc
    wcel
    cP
    cc
    wcel
    #
    @66
    @67
    wceq
    neg1cn
    @68
    @57
    cP
    addcom
    sylancr
    @4
    @69
    @33
    @67
    @1
    wceq
    @68
    ax-1cn
    cP
    c1
    negsub
    sylancl
    3eqtrd
    oveq1d
    @4
    @57
    cr
    wcel
    #
    @47
    @44
    @64
    @58
    wceq
    @70
    @4
    neg1rr
    a1i
    @50
    @46
    @57
    cP
    c1
    modcyc
    syl3anc
    @4
    @1
    cr
    wcel
    #
    @47
    cc0
    @1
    cle
    wbr
    @1
    cP
    clt
    wbr
    @65
    @1
    wceq
    @4
    @53
    @71
    @55
    cP
    peano2rem
    syl
    @50
    @4
    @1
    @4
    @39
    @1
    cn0
    wcel
    @45
    cP
    nnm1nn0
    syl
    nn0ge0d
    @4
    cP
    @55
    ltm1d
    @1
    cP
    modid
    syl22anc
    3eqtr3d
    eqeq12d
    @4
    @60
    @9
    cP
    cdvds
    @4
    @32
    @33
    @60
    @9
    wceq
    @34
    ax-1cn
    cN
    c1
    subneg
    sylancl
    breq2d
    3bitr3rd
    orbi12d
    bitrd
end
