include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cun.mm"
include "wceq.mm"
include "w3a.mm"
include "caddc.mm"
include "cfv.mm"
include "cres.mm"
include "wa.mm"
include "csn.mm"
include "cin.mm"
include "c0.mm"
include "simpr1.mm"
include "cn.mm"
include "nn0p1nn.mm"
include "adantr.mm"
include "simpr2.mm"
include "cop.mm"
include "fsng.mm"
include "mpbiri.mm"
include "syl2anc.mm"
include "snssd.mm"
include "fssd.mm"
include "fzp1disj.mm"
include "a1i.mm"
include "fun2.mm"
include "syl21anc.mm"
include "cz.mm"
include "cmin.mm"
include "cuz.mm"
include "1z.mm"
include "simpl.mm"
include "cc0.mm"
include "nn0uz.mm"
include "1m1e0.mm"
include "fveq2i.mm"
include "eqtr4i.mm"
include "syl6eleq.mm"
include "fzsuc2.mm"
include "sylancr.mm"
include "eqcomd.mm"
include "feq2d.mm"
include "mpbid.mm"
include "simpr3.mm"
include "feq1d.mm"
include "mpbird.mm"
include "ovex.mm"
include "snid.mm"
include "fvres.mm"
include "ax-mp.mm"
include "reseq1d.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "fnresdisj.mm"
include "3syl.mm"
include "uneq1d.mm"
include "resundir.mm"
include "uncom.mm"
include "un0.mm"
include "eqtr2i.mm"
include "3eqtr4g.mm"
include "fnresdm.mm"
include "3eqtrd.mm"
include "fveq1d.mm"
include "fveq1i.mm"
include "fvsng.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "syl5eqr.mm"
include "incom.mm"
include "uneq2d.mm"
include "eqcomi.mm"
include "3eqtrrd.mm"
include "3jca.mm"
include "wss.mm"
include "fzssp1.mm"
include "fssres.mm"
include "sylancl.mm"
include "nnuz.mm"
include "eluzfz2.mm"
include "syl.mm"
include "ffvelrnd.mm"
include "eqeltrrd.mm"
include "fnressn.mm"
include "opeq2.mm"
include "sneqd.mm"
include "syl6reqr.mm"
include "uneq12d.mm"
include "reseq2d.mm"
include "resundi.mm"
include "syl6req.mm"
include "impbida.mm"

theorem fseq1p1m1
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cH: class H
  let cN: class N
  assume fseq1p1m1.1: |- H = { <. ( N + 1 ) , B >. }


  assert |- ( N e. NN0 -> ( ( F : ( 1 ... N ) --> A /\ B e. A /\ G = ( F u. H ) ) <-> ( G : ( 1 ... ( N + 1 ) ) --> A /\ ( G ` ( N + 1 ) ) = B /\ F = ( G |` ( 1 ... N ) ) ) ) )

  proof
    cN
    cn0
    wcel
    #
    c1
    cN
    cfz
    co
    #
    cA
    cF
    wf
    #
    cB
    cA
    wcel
    #
    cG
    cF
    cH
    cun
    #
    wceq
    #
    w3a
    #
    c1
    cN
    c1
    caddc
    co
    #
    cfz
    co
    #
    cA
    cG
    wf
    #
    @7
    cG
    cfv
    #
    cB
    wceq
    #
    cF
    cG
    @1
    cres
    #
    wceq
    #
    w3a
    #
    @0
    @6
    wa
    #
    @9
    @11
    @13
    @15
    @9
    @8
    cA
    @4
    wf
    #
    @15
    @1
    @7
    csn
    #
    cun
    #
    cA
    @4
    wf
    #
    @16
    @15
    @2
    @17
    cA
    cH
    wf
    #
    @1
    @17
    cin
    #
    c0
    wceq
    #
    @19
    @0
    @2
    @3
    @5
    simpr1
    #
    @15
    @17
    cB
    csn
    #
    cA
    cH
    @15
    @7
    cn
    wcel
    #
    @3
    @17
    @24
    cH
    wf
    #
    @0
    @25
    @6
    cN
    nn0p1nn
    #
    adantr
    #
    @0
    @2
    @3
    @5
    simpr2
    #
    @25
    @3
    wa
    #
    @26
    cH
    @7
    cB
    cop
    #
    csn
    #
    wceq
    fseq1p1m1.1
    @7
    cB
    cn
    cA
    cH
    fsng
    mpbiri
    syl2anc
    #
    @15
    cB
    cA
    @29
    snssd
    fssd
    #
    @22
    @15
    c1
    cN
    fzp1disj
    a1i
    #
    @1
    @17
    cA
    cF
    cH
    fun2
    syl21anc
    @15
    @18
    @8
    cA
    @4
    @15
    @8
    @18
    @15
    c1
    cz
    wcel
    #
    cN
    c1
    c1
    cmin
    co
    #
    cuz
    cfv
    #
    wcel
    #
    @8
    @18
    wceq
    #
    1z
    @15
    cN
    cn0
    @38
    @0
    @6
    simpl
    cn0
    cc0
    cuz
    cfv
    @38
    nn0uz
    @37
    cc0
    cuz
    1m1e0
    fveq2i
    eqtr4i
    #
    syl6eleq
    c1
    cN
    fzsuc2
    #
    sylancr
    eqcomd
    feq2d
    mpbid
    @15
    @8
    cA
    cG
    @4
    @0
    @2
    @3
    @5
    simpr3
    #
    feq1d
    mpbird
    @15
    @10
    @7
    cG
    @17
    cres
    #
    cfv
    #
    cB
    @7
    @17
    wcel
    @45
    @10
    wceq
    @7
    cN
    c1
    caddc
    ovex
    snid
    @7
    @17
    cG
    fvres
    ax-mp
    @15
    @45
    @7
    cH
    cfv
    #
    cB
    @15
    @7
    @44
    cH
    @15
    @44
    @4
    @17
    cres
    #
    cH
    @17
    cres
    #
    cH
    @15
    cG
    @4
    @17
    @43
    reseq1d
    @15
    cF
    @17
    cres
    #
    @48
    cun
    c0
    @48
    cun
    #
    @47
    @48
    @15
    @49
    c0
    @48
    @15
    @22
    @49
    c0
    wceq
    #
    @35
    @15
    @2
    cF
    @1
    wfn
    #
    @22
    @51
    wb
    @23
    @1
    cA
    cF
    ffn
    #
    @1
    @17
    cF
    fnresdisj
    3syl
    mpbid
    uneq1d
    cF
    cH
    @17
    resundir
    @50
    @48
    c0
    cun
    @48
    c0
    @48
    uncom
    @48
    un0
    eqtr2i
    3eqtr4g
    @15
    @20
    cH
    @17
    wfn
    #
    @48
    cH
    wceq
    @34
    @17
    cA
    cH
    ffn
    @17
    cH
    fnresdm
    3syl
    3eqtrd
    fveq1d
    @15
    @25
    @3
    @46
    cB
    wceq
    @28
    @29
    @30
    @46
    @7
    @32
    cfv
    cB
    @7
    cH
    @32
    fseq1p1m1.1
    fveq1i
    @7
    cB
    cn
    cA
    fvsng
    syl5eq
    syl2anc
    eqtrd
    syl5eqr
    @15
    @12
    @4
    @1
    cres
    #
    cF
    @1
    cres
    #
    cF
    @15
    cG
    @4
    @1
    @43
    reseq1d
    @15
    @56
    cH
    @1
    cres
    #
    cun
    @56
    c0
    cun
    #
    @55
    @56
    @15
    @57
    c0
    @56
    @15
    @17
    @1
    cin
    #
    c0
    wceq
    #
    @57
    c0
    wceq
    #
    @15
    @59
    @21
    c0
    @17
    @1
    incom
    @35
    syl5eq
    @15
    @26
    @54
    @60
    @61
    wb
    @33
    @17
    @24
    cH
    ffn
    @17
    @1
    cH
    fnresdisj
    3syl
    mpbid
    uneq2d
    cF
    cH
    @1
    resundir
    @58
    @56
    @56
    un0
    eqcomi
    3eqtr4g
    @15
    @2
    @52
    @56
    cF
    wceq
    @23
    @53
    @1
    cF
    fnresdm
    3syl
    3eqtrrd
    3jca
    @0
    @14
    wa
    #
    @2
    @3
    @5
    @62
    @2
    @1
    cA
    @12
    wf
    #
    @62
    @9
    @1
    @8
    wss
    @63
    @0
    @9
    @11
    @13
    simpr1
    #
    c1
    cN
    fzssp1
    @8
    cA
    @1
    cG
    fssres
    sylancl
    @62
    @1
    cA
    cF
    @12
    @0
    @9
    @11
    @13
    simpr3
    #
    feq1d
    mpbird
    @62
    @10
    cB
    cA
    @0
    @9
    @11
    @13
    simpr2
    #
    @62
    @8
    cA
    @7
    cG
    @64
    @62
    @7
    c1
    cuz
    cfv
    #
    wcel
    @7
    @8
    wcel
    #
    @62
    @7
    cn
    @67
    @0
    @25
    @14
    @27
    adantr
    nnuz
    syl6eleq
    c1
    @7
    eluzfz2
    syl
    #
    ffvelrnd
    eqeltrrd
    @62
    @4
    @12
    @44
    cun
    #
    cG
    @8
    cres
    #
    cG
    @62
    cF
    @12
    cH
    @44
    @65
    @62
    @44
    @32
    cH
    @62
    @44
    @7
    @10
    cop
    #
    csn
    #
    @32
    @62
    cG
    @8
    wfn
    #
    @68
    @44
    @73
    wceq
    @62
    @9
    @74
    @64
    @8
    cA
    cG
    ffn
    #
    syl
    @69
    @8
    @7
    cG
    fnressn
    syl2anc
    @62
    @11
    @73
    @32
    wceq
    @66
    @11
    @72
    @31
    @10
    cB
    @7
    opeq2
    sneqd
    syl
    eqtrd
    fseq1p1m1.1
    syl6reqr
    uneq12d
    @62
    @71
    cG
    @18
    cres
    @70
    @62
    @8
    @18
    cG
    @62
    @36
    @39
    @40
    1z
    @62
    cN
    cn0
    @38
    @0
    @14
    simpl
    @41
    syl6eleq
    @42
    sylancr
    reseq2d
    cG
    @1
    @17
    resundi
    syl6req
    @62
    @9
    @74
    @71
    cG
    wceq
    @64
    @75
    @8
    cG
    fnresdm
    3syl
    3eqtrrd
    3jca
    impbida
end
