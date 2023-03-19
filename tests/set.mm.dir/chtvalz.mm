include "cz.mm"
include "wcel.mm"
include "ccht.mm"
include "cfv.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "cprime.mm"
include "cin.mm"
include "cv.mm"
include "clog.mm"
include "csu.mm"
include "c1.mm"
include "cfz.mm"
include "cr.mm"
include "wceq.mm"
include "zre.mm"
include "chtval.mm"
include "syl.mm"
include "cn.mm"
include "wn.mm"
include "c2.mm"
include "nnz.mm"
include "cfl.mm"
include "ppisval.mm"
include "flid.mm"
include "oveq2d.mm"
include "ineq1d.mm"
include "eqtrd.mm"
include "cdif.mm"
include "c0.mm"
include "wss.mm"
include "cuz.mm"
include "2nn.mm"
include "nnuz.mm"
include "eleqtri.mm"
include "fzss1.mm"
include "ax-mp.mm"
include "ssdif0.mm"
include "mpbi.mm"
include "ineq1i.mm"
include "0in.mm"
include "eqtri.mm"
include "a1i.mm"
include "csn.mm"
include "caddc.mm"
include "cun.mm"
include "eleq2i.mm"
include "fzpred.mm"
include "sylbi.mm"
include "eqcomd.mm"
include "1p1e2.mm"
include "oveq1i.mm"
include "difeq12d.mm"
include "difun2.mm"
include "fzpreddisj.mm"
include "disjdif2.mm"
include "syl5eq.mm"
include "eqtr3d.mm"
include "incom.mm"
include "1nprm.mm"
include "disjsn.mm"
include "mpbir.mm"
include "eqtr3i.mm"
include "syl6eq.mm"
include "difininv.mm"
include "syl2anc.mm"
include "adantl.mm"
include "clt.mm"
include "wbr.mm"
include "znnnlt1.mm"
include "biimpa.mm"
include "wa.mm"
include "cpnf.mm"
include "cico.mm"
include "cdvds.mm"
include "cmin.mm"
include "wral.mm"
include "isprm3.mm"
include "simplbi.mm"
include "ssriv.mm"
include "nnzi.mm"
include "uzssico.mm"
include "sstri.mm"
include "cxr.mm"
include "cle.mm"
include "0xr.mm"
include "nnrei.mm"
include "rexri.mm"
include "0le0.mm"
include "adantr.mm"
include "1red.mm"
include "simpr.mm"
include "1lt2.mm"
include "lttrd.mm"
include "iccssico.mm"
include "syl22anc.mm"
include "pnfxr.mm"
include "icodisj.mm"
include "mp3an.mm"
include "ssdisj.mm"
include "sylancl.mm"
include "syl5eqr.mm"
include "sylancr.mm"
include "1zzd.mm"
include "simpl.mm"
include "fzn.mm"
include "syl21anc.mm"
include "eqtr4d.mm"
include "syldan.mm"
include "exmidd.mm"
include "mpjaodan.mm"
include "sumeq1d.mm"

theorem chtvalz
  let vn: setvar n
  let cN: class N
  let vi: setvar i

  disjoint N n
  disjoint i n
  assert |- ( N e. ZZ -> ( theta ` N ) = sum_ n e. ( ( 1 ... N ) i^i Prime ) ( log ` n ) )

  proof
    cN
    cz
    wcel
    #
    cN
    ccht
    cfv
    #
    cc0
    cN
    cicc
    co
    #
    cprime
    cin
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
    c1
    cN
    cfz
    co
    #
    cprime
    cin
    #
    @5
    vn
    csu
    @0
    cN
    cr
    wcel
    #
    @1
    @6
    wceq
    cN
    zre
    #
    cN
    vn
    chtval
    syl
    @0
    @3
    @8
    @5
    vn
    @0
    cN
    cn
    wcel
    #
    @3
    @8
    wceq
    #
    @11
    wn
    #
    @11
    @12
    @0
    @11
    @3
    c2
    cN
    cfz
    co
    #
    cprime
    cin
    #
    @8
    @11
    @0
    @3
    @15
    wceq
    cN
    nnz
    @0
    @3
    c2
    cN
    cfl
    cfv
    #
    cfz
    co
    #
    cprime
    cin
    #
    @15
    @0
    @9
    @3
    @18
    wceq
    @10
    cN
    ppisval
    syl
    @0
    @17
    @14
    cprime
    @0
    @16
    cN
    c2
    cfz
    cN
    flid
    oveq2d
    ineq1d
    eqtrd
    syl
    @11
    @14
    @7
    cdif
    #
    cprime
    cin
    #
    c0
    wceq
    #
    @7
    @14
    cdif
    #
    cprime
    cin
    #
    c0
    wceq
    @15
    @8
    wceq
    @21
    @11
    @20
    c0
    cprime
    cin
    #
    c0
    @19
    c0
    cprime
    @14
    @7
    wss
    #
    @19
    c0
    wceq
    c2
    c1
    cuz
    cfv
    #
    wcel
    @25
    c2
    cn
    @26
    2nn
    nnuz
    eleqtri
    c2
    c1
    cN
    fzss1
    ax-mp
    @14
    @7
    ssdif0
    mpbi
    ineq1i
    cprime
    0in
    #
    eqtri
    a1i
    @11
    @23
    c1
    csn
    #
    cprime
    cin
    #
    c0
    @11
    @22
    @28
    cprime
    @11
    @28
    c1
    c1
    caddc
    co
    #
    cN
    cfz
    co
    #
    cun
    #
    @31
    cdif
    #
    @22
    @28
    @11
    @32
    @7
    @31
    @14
    @11
    @7
    @32
    @11
    cN
    @26
    wcel
    #
    @7
    @32
    wceq
    cn
    @26
    cN
    nnuz
    eleq2i
    #
    c1
    cN
    fzpred
    sylbi
    eqcomd
    @31
    @14
    wceq
    @11
    @30
    c2
    cN
    cfz
    1p1e2
    oveq1i
    a1i
    difeq12d
    @11
    @33
    @28
    @31
    cdif
    #
    @28
    @28
    @31
    difun2
    @11
    @28
    @31
    cin
    c0
    wceq
    #
    @36
    @28
    wceq
    @11
    @34
    @37
    @35
    c1
    cN
    fzpreddisj
    sylbi
    @28
    @31
    disjdif2
    syl
    syl5eq
    eqtr3d
    ineq1d
    cprime
    @28
    cin
    #
    @29
    c0
    cprime
    @28
    incom
    @38
    c0
    wceq
    c1
    cprime
    wcel
    wn
    1nprm
    cprime
    c1
    disjsn
    mpbir
    eqtr3i
    syl6eq
    @14
    cprime
    @7
    difininv
    syl2anc
    eqtrd
    adantl
    @0
    @13
    cN
    c1
    clt
    wbr
    #
    @12
    @0
    @13
    @39
    cN
    znnnlt1
    biimpa
    @0
    @39
    wa
    #
    @3
    c0
    @8
    @40
    @3
    cprime
    @2
    cin
    #
    c0
    @2
    cprime
    incom
    @40
    cprime
    c2
    cpnf
    cico
    co
    #
    wss
    @42
    @2
    cin
    #
    c0
    wceq
    @41
    c0
    wceq
    cprime
    c2
    cuz
    cfv
    #
    @42
    vn
    cprime
    @44
    @4
    cprime
    wcel
    @4
    @44
    wcel
    vi
    cv
    @4
    cdvds
    wbr
    wn
    vi
    c2
    @4
    c1
    cmin
    co
    cfz
    co
    wral
    vi
    @4
    isprm3
    simplbi
    ssriv
    c2
    cz
    wcel
    @44
    @42
    wss
    c2
    2nn
    nnzi
    c2
    uzssico
    ax-mp
    sstri
    @40
    @43
    @2
    @42
    cin
    #
    c0
    @2
    @42
    incom
    @40
    @2
    cc0
    c2
    cico
    co
    #
    wss
    #
    @46
    @42
    cin
    c0
    wceq
    #
    @45
    c0
    wceq
    @40
    cc0
    cxr
    wcel
    #
    c2
    cxr
    wcel
    #
    cc0
    cc0
    cle
    wbr
    #
    cN
    c2
    clt
    wbr
    @47
    @49
    @40
    0xr
    a1i
    @50
    @40
    c2
    c2
    2nn
    nnrei
    #
    rexri
    #
    a1i
    @51
    @40
    0le0
    a1i
    @40
    cN
    c1
    c2
    @0
    @9
    @39
    @10
    adantr
    @40
    1red
    c2
    cr
    wcel
    @40
    @52
    a1i
    @0
    @39
    simpr
    #
    c1
    c2
    clt
    wbr
    @40
    1lt2
    a1i
    lttrd
    cc0
    c2
    cc0
    cN
    iccssico
    syl22anc
    @49
    @50
    cpnf
    cxr
    wcel
    @48
    0xr
    @53
    pnfxr
    cc0
    c2
    cpnf
    icodisj
    mp3an
    @2
    @46
    @42
    ssdisj
    sylancl
    syl5eqr
    cprime
    @42
    @2
    ssdisj
    sylancr
    syl5eq
    @40
    @8
    @24
    c0
    @40
    @7
    c0
    cprime
    @40
    c1
    cz
    wcel
    #
    @0
    @39
    @7
    c0
    wceq
    #
    @40
    1zzd
    @0
    @39
    simpl
    @54
    @55
    @0
    wa
    @39
    @56
    c1
    cN
    fzn
    biimpa
    syl21anc
    ineq1d
    @27
    syl6eq
    eqtr4d
    syldan
    @0
    @11
    exmidd
    mpjaodan
    sumeq1d
    eqtrd
end
