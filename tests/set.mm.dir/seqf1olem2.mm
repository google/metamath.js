include "cfz.mm"
include "co.mm"
include "cres.mm"
include "ccom.mm"
include "cseq.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wf1o.mm"
include "wf.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "cfn.mm"
include "wfn.mm"
include "wss.mm"
include "ffn.mm"
include "syl.mm"
include "fzssp1.mm"
include "fnssres.mm"
include "sylancl.mm"
include "fzfid.mm"
include "fnfi.mm"
include "syl2anc.mm"
include "elex.mm"
include "seqf1olem1.mm"
include "f1of.mm"
include "fex2.mm"
include "syl3anc.mm"
include "jca.mm"
include "fssres.mm"
include "f1oeq1.mm"
include "feq1.mm"
include "bi2anan9r.mm"
include "coeq1.mm"
include "coeq2.mm"
include "sylan9eq.mm"
include "seqeq3d.mm"
include "fveq1d.mm"
include "simpl.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "spc2gv.mm"
include "syl3c.mm"
include "fvres.mm"
include "adantl.mm"
include "seqfveq.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "adantlr.mm"
include "w3a.mm"
include "cuz.mm"
include "elfzuz3.mm"
include "eluzp1p1.mm"
include "elfzuz.mm"
include "fco.mm"
include "fssd.mm"
include "ffvelrnda.mm"
include "seqsplit.mm"
include "wo.mm"
include "elfzp12.mm"
include "biimpa.mm"
include "sylan.mm"
include "seqeq1.mm"
include "eqcomd.mm"
include "cz.mm"
include "ccnv.mm"
include "f1ocnv.mm"
include "3syl.mm"
include "peano2uz.mm"
include "eluzfz2.mm"
include "ffvelrnd.mm"
include "syl5eqel.mm"
include "elfzelz.mm"
include "seq1.mm"
include "sylan9eqr.mm"
include "simpr.mm"
include "eluzfz1.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "fzss1.mm"
include "seqf1olem2a.mm"
include "1zzd.mm"
include "sselda.mm"
include "syldan.mm"
include "clt.mm"
include "wbr.mm"
include "cif.mm"
include "breq1.mm"
include "id.mm"
include "oveq1.mm"
include "ifbieq12d.mm"
include "fveq2d.mm"
include "fvex.mm"
include "fvmpt.mm"
include "wn.mm"
include "cle.mm"
include "elfzle1.mm"
include "cr.mm"
include "zred.mm"
include "lenltd.mm"
include "mpbid.mm"
include "iffalse.mm"
include "fvco3.mm"
include "fzp1elp1.mm"
include "3eqtr4d.mm"
include "seqshft2.mm"
include "fveq2i.mm"
include "f1ocnvfv2.mm"
include "syl5eq.mm"
include "eqtr2d.mm"
include "oveq12d.mm"
include "eqtr4d.mm"
include "seqeq1d.mm"
include "3eqtrd.mm"
include "cmin.mm"
include "eluzel2.mm"
include "eluzp1m1.mm"
include "syl2an.mm"
include "cc.mm"
include "eluzelz.mm"
include "zcnd.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "peano2zm.mm"
include "npcan.mm"
include "eleqtrrd.mm"
include "eqeltrrd.mm"
include "fzss2.mm"
include "wb.mm"
include "elfzm11.mm"
include "simp3d.mm"
include "iftrue.mm"
include "fzp1ss.mm"
include "seqcl.mm"
include "sseldd.mm"
include "3jca.mm"
include "caovassg.mm"
include "seqm1.mm"
include "oveq2d.mm"
include "jaodan.mm"
include "seqp1.mm"
include "peano2re.mm"
include "elfzle2.mm"
include "ltp1d.mm"
include "lelttrd.mm"
include "simplr.mm"
include "breqtrrd.mm"
include "wne.mm"
include "gtned.mm"
include "ad2antrr.mm"
include "fzelp1.mm"
include "elfzp1.mm"
include "ord.mm"
include "f1ocnvfv.mm"
include "eqeq1i.mm"
include "syl6ibr.mm"
include "syld.mm"
include "necon1ad.mm"
include "mpd.mm"
include "syl5eqr.mm"
include "eqtr3d.mm"
include "mpjaodan.mm"

theorem seqf1olem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let c.pl: class .+
  let cS: class S
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let cH: class H
  assume seqf1o.1: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x .+ y ) e. S )
  assume seqf1o.2: |- ( ( ph /\ ( x e. C /\ y e. C ) ) -> ( x .+ y ) = ( y .+ x ) )
  assume seqf1o.3: |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x .+ y ) .+ z ) = ( x .+ ( y .+ z ) ) )
  assume seqf1o.4: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume seqf1o.5: |- ( ph -> C C_ S )
  assume seqf1olem.5: |- ( ph -> F : ( M ... ( N + 1 ) ) -1-1-onto-> ( M ... ( N + 1 ) ) )
  assume seqf1olem.6: |- ( ph -> G : ( M ... ( N + 1 ) ) --> C )
  assume seqf1olem.7: |- J = ( k e. ( M ... N ) |-> ( F ` if ( k < K , k , ( k + 1 ) ) ) )
  assume seqf1olem.8: |- K = ( `' F ` ( N + 1 ) )
  assume seqf1olem.9: |- ( ph -> A. g A. f ( ( f : ( M ... N ) -1-1-onto-> ( M ... N ) /\ g : ( M ... N ) --> C ) -> ( seq M ( .+ , ( g o. f ) ) ` N ) = ( seq M ( .+ , g ) ` N ) ) )

  disjoint f g
  disjoint f k
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint g k
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint F g
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G f
  disjoint G g
  disjoint G k
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint M f
  disjoint M g
  disjoint M k
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint .+ f
  disjoint .+ g
  disjoint .+ k
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint J f
  disjoint J g
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint N f
  disjoint N g
  disjoint N k
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint K k
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint f ph
  disjoint g ph
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint S k
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint C f
  disjoint C g
  disjoint C k
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint f m
  disjoint f n
  disjoint g m
  disjoint g n
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint G m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint G n
  disjoint f s
  disjoint f t
  disjoint f w
  disjoint g s
  disjoint g t
  disjoint g w
  disjoint k s
  disjoint k t
  disjoint k w
  disjoint m s
  disjoint m t
  disjoint m w
  disjoint M m
  disjoint n s
  disjoint n t
  disjoint n w
  disjoint M n
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint M s
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint M t
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint M w
  disjoint .+ m
  disjoint .+ n
  disjoint .+ s
  disjoint .+ t
  disjoint .+ w
  disjoint N m
  disjoint N n
  disjoint K m
  disjoint K n
  disjoint m ph
  disjoint n ph
  disjoint ph s
  disjoint ph t
  disjoint ph w
  disjoint S s
  disjoint S t
  disjoint S w
  disjoint C s
  disjoint C t
  disjoint C w
  disjoint H k
  assert |- ( ph -> ( seq M ( .+ , ( G o. F ) ) ` ( N + 1 ) ) = ( seq M ( .+ , G ) ` ( N + 1 ) ) )

  proof
    wph
    cN
    c.pl
    cG
    cM
    cN
    cfz
    co
    #
    cres
    #
    cJ
    ccom
    #
    cM
    cseq
    #
    cfv
    #
    cN
    c1
    caddc
    co
    #
    cG
    cfv
    #
    c.pl
    co
    #
    cN
    c.pl
    cG
    cM
    cseq
    #
    cfv
    #
    @6
    c.pl
    co
    #
    @5
    c.pl
    cG
    cF
    ccom
    #
    cM
    cseq
    #
    cfv
    #
    @5
    @8
    cfv
    #
    wph
    @4
    @9
    @6
    c.pl
    wph
    @4
    cN
    c.pl
    @1
    cM
    cseq
    #
    cfv
    #
    @9
    wph
    @1
    cvv
    wcel
    #
    cJ
    cvv
    wcel
    #
    wa
    @0
    @0
    vf
    cv
    #
    wf1o
    #
    @0
    cC
    vg
    cv
    #
    wf
    #
    wa
    #
    cN
    c.pl
    @21
    @19
    ccom
    #
    cM
    cseq
    #
    cfv
    #
    cN
    c.pl
    @21
    cM
    cseq
    #
    cfv
    #
    wceq
    #
    wi
    #
    vf
    wal
    vg
    wal
    @0
    @0
    cJ
    wf1o
    #
    @0
    cC
    @1
    wf
    #
    wa
    #
    @4
    @16
    wceq
    #
    wph
    @17
    @18
    wph
    @1
    cfn
    wcel
    #
    @17
    wph
    @1
    @0
    wfn
    #
    @0
    cfn
    wcel
    #
    @35
    wph
    cG
    cM
    @5
    cfz
    co
    #
    wfn
    #
    @0
    @38
    wss
    #
    @36
    wph
    @38
    cC
    cG
    wf
    #
    @39
    seqf1olem.6
    @38
    cC
    cG
    ffn
    syl
    cM
    cN
    fzssp1
    #
    @38
    @0
    cG
    fnssres
    sylancl
    wph
    cM
    cN
    fzfid
    #
    @0
    @1
    fnfi
    syl2anc
    @1
    cfn
    elex
    syl
    wph
    @0
    @0
    cJ
    wf
    #
    @37
    @37
    @18
    wph
    @31
    @44
    wph
    vx
    vy
    vz
    cC
    c.pl
    cS
    vk
    cF
    cG
    cJ
    cK
    cM
    cN
    seqf1o.1
    seqf1o.2
    seqf1o.3
    seqf1o.4
    seqf1o.5
    seqf1olem.5
    seqf1olem.6
    seqf1olem.7
    seqf1olem.8
    seqf1olem1
    #
    @0
    @0
    cJ
    f1of
    syl
    #
    @43
    @43
    @0
    @0
    cJ
    cfn
    cfn
    fex2
    syl3anc
    jca
    seqf1olem.9
    wph
    @31
    @32
    @45
    wph
    @41
    @40
    @32
    seqf1olem.6
    @42
    @38
    cC
    @0
    cG
    fssres
    sylancl
    jca
    @30
    @33
    @34
    wi
    vg
    vf
    @1
    cJ
    cvv
    cvv
    @21
    @1
    wceq
    #
    @19
    cJ
    wceq
    #
    wa
    #
    @23
    @33
    @29
    @34
    @48
    @20
    @31
    @47
    @22
    @32
    @0
    @0
    @19
    cJ
    f1oeq1
    @0
    cC
    @21
    @1
    feq1
    bi2anan9r
    @49
    @26
    @4
    @28
    @16
    @49
    cN
    @25
    @3
    @49
    @24
    @2
    c.pl
    cM
    @47
    @48
    @24
    @1
    @19
    ccom
    @2
    @21
    @1
    @19
    coeq1
    @19
    cJ
    @1
    coeq2
    sylan9eq
    seqeq3d
    fveq1d
    @49
    cN
    @27
    @15
    @49
    @21
    @1
    c.pl
    cM
    @47
    @48
    simpl
    seqeq3d
    fveq1d
    eqeq12d
    imbi12d
    spc2gv
    syl3c
    wph
    c.pl
    vx
    @1
    cG
    cM
    cN
    seqf1o.4
    vx
    cv
    #
    @0
    wcel
    #
    @50
    @1
    cfv
    @50
    cG
    cfv
    wceq
    wph
    @50
    @0
    cG
    fvres
    adantl
    seqfveq
    eqtrd
    oveq1d
    wph
    cK
    @0
    wcel
    #
    @13
    @7
    wceq
    cK
    @5
    wceq
    #
    wph
    @52
    wa
    #
    @13
    cK
    @12
    cfv
    #
    @5
    c.pl
    @11
    cK
    c1
    caddc
    co
    #
    cseq
    cfv
    #
    c.pl
    co
    #
    @7
    @54
    vx
    vy
    vz
    c.pl
    cS
    @11
    cM
    cK
    @5
    wph
    @50
    cS
    wcel
    #
    vy
    cv
    #
    cS
    wcel
    #
    wa
    #
    @50
    @60
    c.pl
    co
    #
    cS
    wcel
    #
    @52
    seqf1o.1
    adantlr
    #
    wph
    @59
    @61
    vz
    cv
    #
    cS
    wcel
    w3a
    #
    @63
    @66
    c.pl
    co
    @50
    @60
    @66
    c.pl
    co
    c.pl
    co
    wceq
    #
    @52
    seqf1o.3
    adantlr
    #
    @54
    cN
    cK
    cuz
    cfv
    #
    wcel
    #
    @5
    @56
    cuz
    cfv
    wcel
    @52
    @71
    wph
    cK
    cM
    cN
    elfzuz3
    adantl
    #
    cK
    cN
    eluzp1p1
    syl
    #
    @52
    cK
    cM
    cuz
    cfv
    #
    wcel
    #
    wph
    cK
    cM
    cN
    elfzuz
    adantl
    #
    wph
    @50
    @38
    wcel
    #
    @50
    @11
    cfv
    #
    cS
    wcel
    #
    @52
    wph
    @38
    cS
    @50
    @11
    wph
    @38
    cC
    cS
    @11
    wph
    @41
    @38
    @38
    cF
    wf
    #
    @38
    cC
    @11
    wf
    #
    seqf1olem.6
    wph
    @38
    @38
    cF
    wf1o
    #
    @80
    seqf1olem.5
    @38
    @38
    cF
    f1of
    syl
    #
    @38
    @38
    cC
    cG
    cF
    fco
    syl2anc
    #
    seqf1o.5
    fssd
    ffvelrnda
    #
    adantlr
    #
    seqsplit
    wph
    @52
    cK
    cM
    wceq
    #
    cK
    cM
    c1
    caddc
    co
    #
    cN
    cfz
    co
    #
    wcel
    #
    wo
    #
    @58
    @7
    wceq
    #
    wph
    cN
    @74
    wcel
    #
    @52
    @91
    seqf1o.4
    @93
    @52
    @91
    cK
    cM
    cN
    elfzp12
    biimpa
    sylan
    wph
    @87
    @92
    @90
    wph
    @87
    wa
    #
    @58
    cK
    @11
    cfv
    #
    @57
    c.pl
    co
    #
    cN
    c.pl
    @2
    cK
    cseq
    #
    cfv
    #
    @6
    c.pl
    co
    #
    @7
    @94
    @55
    @95
    @57
    c.pl
    @87
    wph
    @55
    cK
    c.pl
    @11
    cK
    cseq
    #
    cfv
    #
    @95
    @87
    cK
    @12
    @100
    @87
    @100
    @12
    c.pl
    @11
    cK
    cM
    seqeq1
    eqcomd
    fveq1d
    wph
    cK
    @38
    wcel
    #
    cK
    cz
    wcel
    #
    @101
    @95
    wceq
    wph
    cK
    @5
    cF
    ccnv
    #
    cfv
    #
    @38
    seqf1olem.8
    wph
    @38
    @38
    @5
    @104
    wph
    @82
    @38
    @38
    @104
    wf1o
    @38
    @38
    @104
    wf
    seqf1olem.5
    @38
    @38
    cF
    f1ocnv
    @38
    @38
    @104
    f1of
    3syl
    wph
    @93
    @5
    @74
    wcel
    @5
    @38
    wcel
    #
    seqf1o.4
    cM
    cN
    peano2uz
    cM
    @5
    eluzfz2
    3syl
    #
    ffvelrnd
    syl5eqel
    #
    cK
    cM
    @5
    elfzelz
    #
    c.pl
    @11
    cK
    seq1
    3syl
    sylan9eqr
    oveq1d
    wph
    @87
    @52
    @96
    @99
    wceq
    #
    @94
    cK
    cM
    @0
    wph
    @87
    simpr
    #
    wph
    cM
    @0
    wcel
    #
    @87
    wph
    @93
    @112
    seqf1o.4
    cM
    cN
    eluzfz1
    syl
    adantr
    eqeltrd
    @54
    @96
    @57
    @95
    c.pl
    co
    @99
    @54
    vx
    vy
    vz
    @38
    cC
    c.pl
    cS
    @11
    cK
    @56
    @5
    @65
    wph
    @50
    cC
    wcel
    @60
    cC
    wcel
    wa
    @63
    @60
    @50
    c.pl
    co
    wceq
    @52
    seqf1o.2
    adantlr
    @69
    @73
    wph
    cC
    cS
    wss
    @52
    seqf1o.5
    adantr
    wph
    @81
    @52
    @84
    adantr
    wph
    @102
    @52
    @108
    adantr
    @54
    @75
    @56
    @74
    wcel
    @56
    @5
    cfz
    co
    #
    @38
    wss
    @76
    cM
    cK
    peano2uz
    @56
    cM
    @5
    fzss1
    3syl
    #
    seqf1olem2a
    @54
    @98
    @57
    @6
    @95
    c.pl
    @54
    c.pl
    vx
    @2
    @11
    c1
    cK
    cN
    @72
    @54
    1zzd
    wph
    @50
    cK
    cN
    cfz
    co
    #
    wcel
    #
    @50
    @2
    cfv
    #
    @50
    c1
    caddc
    co
    #
    @11
    cfv
    #
    wceq
    @52
    wph
    @116
    wa
    #
    @50
    cJ
    cfv
    #
    @1
    cfv
    #
    @118
    cF
    cfv
    #
    cG
    cfv
    #
    @117
    @119
    @120
    @122
    @121
    cG
    cfv
    #
    @124
    @120
    @121
    @0
    wcel
    #
    @122
    @125
    wceq
    #
    wph
    @116
    @51
    @126
    wph
    @115
    @0
    @50
    wph
    @102
    @75
    @115
    @0
    wss
    @108
    cK
    cM
    @5
    elfzuz
    cK
    cM
    cN
    fzss1
    3syl
    sselda
    #
    wph
    @0
    @0
    @50
    cJ
    @46
    ffvelrnda
    #
    syldan
    @121
    @0
    cG
    fvres
    #
    syl
    @120
    @121
    @123
    cG
    @120
    @121
    @50
    cK
    clt
    wbr
    #
    @50
    @118
    cif
    #
    cF
    cfv
    #
    @123
    @120
    @51
    @121
    @133
    wceq
    #
    @128
    vk
    @50
    vk
    cv
    #
    cK
    clt
    wbr
    #
    @135
    @135
    c1
    caddc
    co
    #
    cif
    #
    cF
    cfv
    @133
    @0
    cJ
    @135
    @50
    wceq
    #
    @138
    @132
    cF
    @139
    @136
    @131
    @135
    @137
    @50
    @118
    @135
    @50
    cK
    clt
    breq1
    @139
    id
    @135
    @50
    c1
    caddc
    oveq1
    ifbieq12d
    fveq2d
    seqf1olem.7
    @132
    cF
    fvex
    fvmpt
    #
    syl
    @120
    @131
    wn
    #
    @133
    @123
    wceq
    @120
    cK
    @50
    cle
    wbr
    #
    @141
    @116
    @142
    wph
    @50
    cK
    cN
    elfzle1
    adantl
    @120
    cK
    @50
    wph
    cK
    cr
    wcel
    @116
    wph
    cK
    wph
    @102
    @103
    @108
    @109
    syl
    #
    zred
    adantr
    @120
    @50
    @116
    @50
    cz
    wcel
    #
    wph
    @50
    cK
    cN
    elfzelz
    adantl
    zred
    lenltd
    mpbid
    @141
    @132
    @118
    cF
    @131
    @50
    @118
    iffalse
    fveq2d
    syl
    eqtrd
    fveq2d
    eqtrd
    wph
    @116
    @51
    @117
    @122
    wceq
    #
    @128
    wph
    @44
    @51
    @145
    @46
    @0
    @0
    @50
    @1
    cJ
    fvco3
    sylan
    #
    syldan
    wph
    @116
    @118
    @38
    wcel
    #
    @119
    @124
    wceq
    #
    @120
    @51
    @147
    @128
    @50
    cM
    cN
    fzp1elp1
    syl
    wph
    @80
    @147
    @148
    @83
    @38
    @38
    @118
    cG
    cF
    fvco3
    sylan
    syldan
    3eqtr4d
    adantlr
    seqshft2
    wph
    @6
    @95
    wceq
    @52
    wph
    @95
    cK
    cF
    cfv
    #
    cG
    cfv
    #
    @6
    wph
    @80
    @102
    @95
    @150
    wceq
    @83
    @108
    @38
    @38
    cK
    cG
    cF
    fvco3
    syl2anc
    wph
    @149
    @5
    cG
    wph
    @149
    @105
    cF
    cfv
    #
    @5
    cK
    @105
    cF
    seqf1olem.8
    fveq2i
    wph
    @82
    @106
    @151
    @5
    wceq
    #
    seqf1olem.5
    @107
    @38
    @38
    @5
    cF
    f1ocnvfv2
    syl2anc
    #
    syl5eq
    fveq2d
    eqtr2d
    adantr
    oveq12d
    eqtr4d
    #
    syldan
    @94
    @98
    @4
    @6
    c.pl
    @94
    cN
    @97
    @3
    @94
    cK
    cM
    c.pl
    @2
    @111
    seqeq1d
    fveq1d
    oveq1d
    3eqtrd
    wph
    @90
    wa
    #
    cK
    c1
    cmin
    co
    #
    @12
    cfv
    #
    @95
    c.pl
    co
    #
    @57
    c.pl
    co
    #
    @156
    @3
    cfv
    #
    @98
    c.pl
    co
    #
    @6
    c.pl
    co
    #
    @58
    @7
    @155
    @157
    @96
    c.pl
    co
    #
    @160
    @99
    c.pl
    co
    #
    @159
    @162
    @155
    @157
    @160
    @96
    @99
    c.pl
    @155
    c.pl
    vx
    @11
    @2
    cM
    @156
    wph
    cM
    cz
    wcel
    #
    cK
    @88
    cuz
    cfv
    wcel
    #
    @156
    @74
    wcel
    @90
    wph
    @93
    @165
    seqf1o.4
    cM
    cN
    eluzel2
    #
    syl
    #
    cK
    @88
    cN
    elfzuz
    #
    cM
    cK
    eluzp1m1
    syl2an
    #
    wph
    @50
    cM
    @156
    cfz
    co
    #
    wcel
    #
    @78
    @117
    wceq
    @90
    wph
    @172
    wa
    #
    @50
    cF
    cfv
    #
    cG
    cfv
    #
    @122
    @78
    @117
    @173
    @122
    @125
    @175
    @173
    @126
    @127
    wph
    @172
    @51
    @126
    wph
    @171
    @0
    @50
    wph
    cN
    @156
    cuz
    cfv
    #
    wcel
    #
    @171
    @0
    wss
    wph
    @5
    c1
    cmin
    co
    #
    cN
    @176
    wph
    cN
    cc
    wcel
    c1
    cc
    wcel
    #
    @178
    cN
    wceq
    wph
    cN
    wph
    @93
    cN
    cz
    wcel
    seqf1o.4
    cM
    cN
    eluzelz
    syl
    #
    zcnd
    ax-1cn
    cN
    c1
    pncan
    sylancl
    wph
    @156
    cz
    wcel
    #
    @5
    @156
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    @178
    @176
    wcel
    wph
    @102
    @103
    @181
    @108
    @109
    cK
    peano2zm
    3syl
    wph
    @5
    @70
    @183
    wph
    @102
    @5
    @70
    wcel
    @108
    cK
    cM
    @5
    elfzuz3
    syl
    wph
    @182
    cK
    cuz
    wph
    cK
    cc
    wcel
    #
    @179
    @182
    cK
    wceq
    #
    wph
    cK
    @143
    zcnd
    ax-1cn
    cK
    c1
    npcan
    #
    sylancl
    fveq2d
    eleqtrrd
    @156
    @5
    eluzp1m1
    syl2anc
    eqeltrrd
    #
    @156
    cM
    cN
    fzss2
    syl
    sselda
    #
    @129
    syldan
    @130
    syl
    @173
    @121
    @174
    cG
    @173
    @121
    @133
    @174
    @173
    @51
    @134
    @188
    @140
    syl
    @173
    @131
    @133
    @174
    wceq
    #
    @173
    @144
    cM
    @50
    cle
    wbr
    #
    @131
    wph
    @172
    @144
    @190
    @131
    w3a
    #
    wph
    @165
    @103
    @172
    @191
    wb
    @168
    @143
    @50
    cM
    cK
    elfzm11
    syl2anc
    biimpa
    simp3d
    @131
    @132
    @50
    cF
    @131
    @50
    @118
    iftrue
    fveq2d
    #
    syl
    eqtrd
    fveq2d
    eqtr2d
    wph
    @172
    @77
    @78
    @175
    wceq
    #
    wph
    @171
    @38
    @50
    wph
    @177
    @5
    @176
    wcel
    @171
    @38
    wss
    @187
    @156
    cN
    peano2uz
    @156
    cM
    @5
    fzss2
    3syl
    sselda
    #
    wph
    @80
    @77
    @193
    @83
    @38
    @38
    @50
    cG
    cF
    fvco3
    #
    sylan
    syldan
    wph
    @172
    @51
    @145
    @188
    @146
    syldan
    3eqtr4d
    adantlr
    seqfveq
    wph
    @90
    @52
    @110
    wph
    @89
    @0
    cK
    wph
    @93
    @165
    @89
    @0
    wss
    seqf1o.4
    @167
    cM
    cN
    fzp1ss
    3syl
    sselda
    #
    @154
    syldan
    oveq12d
    wph
    @90
    @157
    cS
    wcel
    #
    @95
    cS
    wcel
    #
    @57
    cS
    wcel
    #
    w3a
    @159
    @163
    wceq
    @155
    @197
    @198
    @199
    @155
    vx
    vy
    c.pl
    cS
    @11
    cM
    @156
    @170
    wph
    @172
    @79
    @90
    wph
    @172
    @77
    @79
    @194
    @85
    syldan
    adantlr
    wph
    @62
    @64
    @90
    seqf1o.1
    adantlr
    #
    seqcl
    wph
    @198
    @90
    wph
    cC
    cS
    @95
    seqf1o.5
    wph
    @38
    cC
    cK
    @11
    @84
    @108
    ffvelrnd
    sseldd
    adantr
    wph
    @90
    @52
    @199
    @196
    @54
    vx
    vy
    c.pl
    cS
    @11
    @56
    @5
    @73
    @54
    @50
    @113
    wcel
    @77
    @79
    @54
    @113
    @38
    @50
    @114
    sselda
    @86
    syldan
    @65
    seqcl
    syldan
    3jca
    wph
    vx
    vy
    vz
    @157
    @95
    @57
    cS
    c.pl
    seqf1o.3
    caovassg
    syldan
    wph
    @90
    @160
    cS
    wcel
    #
    @98
    cS
    wcel
    #
    @6
    cS
    wcel
    #
    w3a
    @162
    @164
    wceq
    @155
    @201
    @202
    @203
    @155
    vx
    vy
    c.pl
    cS
    @2
    cM
    @156
    @170
    wph
    @172
    @117
    cS
    wcel
    #
    @90
    wph
    @172
    @51
    @204
    @188
    wph
    @0
    cS
    @50
    @2
    wph
    @0
    cS
    @1
    wf
    #
    @44
    @0
    cS
    @2
    wf
    wph
    @38
    cS
    cG
    wf
    @40
    @205
    wph
    @38
    cC
    cS
    cG
    seqf1olem.6
    seqf1o.5
    fssd
    #
    @42
    @38
    cS
    @0
    cG
    fssres
    sylancl
    @46
    @0
    @0
    cS
    @1
    cJ
    fco
    syl2anc
    ffvelrnda
    #
    syldan
    adantlr
    @200
    seqcl
    @155
    vx
    vy
    c.pl
    cS
    @2
    cK
    cN
    @90
    @71
    wph
    cK
    @88
    cN
    elfzuz3
    adantl
    #
    wph
    @116
    @204
    @90
    wph
    @116
    @51
    @204
    @128
    @207
    syldan
    adantlr
    @200
    seqcl
    wph
    @203
    @90
    wph
    @38
    cS
    @5
    cG
    @206
    @107
    ffvelrnd
    adantr
    3jca
    wph
    vx
    vy
    vz
    @160
    @98
    @6
    cS
    c.pl
    seqf1o.3
    caovassg
    syldan
    3eqtr4d
    @155
    @55
    @158
    @57
    c.pl
    wph
    @165
    @166
    @55
    @158
    wceq
    @90
    @168
    @169
    c.pl
    @11
    cM
    cK
    seqm1
    syl2an
    oveq1d
    @155
    @4
    @161
    @6
    c.pl
    @155
    @4
    @160
    cN
    c.pl
    @2
    @182
    cseq
    #
    cfv
    #
    c.pl
    co
    @161
    @155
    vx
    vy
    vz
    c.pl
    cS
    @2
    cM
    @156
    cN
    @200
    wph
    @67
    @68
    @90
    seqf1o.3
    adantlr
    @155
    cN
    @70
    @183
    @208
    @155
    @182
    cK
    cuz
    @155
    @184
    @179
    @185
    @155
    cK
    @90
    @103
    wph
    cK
    @88
    cN
    elfzelz
    adantl
    zcnd
    ax-1cn
    @186
    sylancl
    #
    fveq2d
    eleqtrrd
    @170
    wph
    @51
    @204
    @90
    @207
    adantlr
    seqsplit
    @155
    @210
    @98
    @160
    c.pl
    @155
    cN
    @209
    @97
    @155
    @182
    cK
    c.pl
    @2
    @211
    seqeq1d
    fveq1d
    oveq2d
    eqtrd
    oveq1d
    3eqtr4d
    jaodan
    syldan
    eqtrd
    wph
    @53
    wa
    #
    @13
    cN
    @12
    cfv
    #
    @5
    @11
    cfv
    #
    c.pl
    co
    #
    @7
    @212
    @93
    @13
    @215
    wceq
    wph
    @93
    @53
    seqf1o.4
    adantr
    #
    c.pl
    @11
    cM
    cN
    seqp1
    syl
    @212
    @213
    @4
    @214
    @6
    c.pl
    @212
    c.pl
    vx
    @11
    @2
    cM
    cN
    @216
    @212
    @51
    wa
    #
    @175
    @122
    @78
    @117
    @217
    @122
    @174
    @1
    cfv
    #
    @175
    @217
    @121
    @174
    @1
    @217
    @121
    @133
    @174
    @51
    @134
    @212
    @140
    adantl
    @217
    @131
    @189
    @217
    @50
    @5
    cK
    clt
    wph
    @51
    @50
    @5
    clt
    wbr
    @53
    wph
    @51
    wa
    #
    @50
    cN
    @5
    @51
    @50
    cr
    wcel
    #
    wph
    @51
    @50
    @50
    cM
    cN
    elfzelz
    zred
    #
    adantl
    wph
    cN
    cr
    wcel
    #
    @51
    wph
    cN
    @180
    zred
    adantr
    #
    @219
    @222
    @5
    cr
    wcel
    @223
    cN
    peano2re
    syl
    @51
    @50
    cN
    cle
    wbr
    wph
    @50
    cM
    cN
    elfzle2
    adantl
    @219
    cN
    @223
    ltp1d
    lelttrd
    adantlr
    wph
    @53
    @51
    simplr
    breqtrrd
    #
    @192
    syl
    eqtrd
    fveq2d
    @217
    @174
    @0
    wcel
    #
    @218
    @175
    wceq
    @217
    cK
    @50
    wne
    @225
    @217
    @50
    cK
    @51
    @220
    @212
    @221
    adantl
    @224
    gtned
    @217
    @225
    cK
    @50
    @217
    @225
    wn
    @174
    @5
    wceq
    #
    cK
    @50
    wceq
    #
    @217
    @225
    @226
    @217
    @174
    @38
    wcel
    #
    @225
    @226
    wo
    #
    @217
    @38
    @38
    @50
    cF
    wph
    @80
    @53
    @51
    @83
    ad2antrr
    @51
    @77
    @212
    @50
    cM
    cN
    fzelp1
    #
    adantl
    #
    ffvelrnd
    @217
    @93
    @228
    @229
    wb
    wph
    @93
    @53
    @51
    seqf1o.4
    ad2antrr
    @174
    cM
    cN
    elfzp1
    syl
    mpbid
    ord
    @217
    @226
    @105
    @50
    wceq
    #
    @227
    @217
    @82
    @77
    @226
    @232
    wi
    wph
    @82
    @53
    @51
    seqf1olem.5
    ad2antrr
    @231
    @38
    @38
    @50
    @5
    cF
    f1ocnvfv
    syl2anc
    cK
    @105
    @50
    seqf1olem.8
    eqeq1i
    syl6ibr
    syld
    necon1ad
    mpd
    @174
    @0
    cG
    fvres
    syl
    eqtr2d
    wph
    @51
    @193
    @53
    wph
    @80
    @77
    @193
    @51
    @83
    @230
    @195
    syl2an
    adantlr
    wph
    @51
    @145
    @53
    @146
    adantlr
    3eqtr4d
    seqfveq
    @212
    @214
    @5
    cF
    cfv
    #
    cG
    cfv
    #
    @6
    wph
    @214
    @234
    wceq
    #
    @53
    wph
    @80
    @106
    @235
    @83
    @107
    @38
    @38
    @5
    cG
    cF
    fvco3
    syl2anc
    adantr
    @212
    @233
    @5
    cG
    @212
    @151
    @233
    @5
    @212
    @105
    @5
    cF
    @212
    @105
    cK
    @5
    seqf1olem.8
    wph
    @53
    simpr
    syl5eqr
    fveq2d
    wph
    @152
    @53
    @153
    adantr
    eqtr3d
    fveq2d
    eqtrd
    oveq12d
    eqtrd
    wph
    @102
    @52
    @53
    wo
    #
    @108
    wph
    @93
    @102
    @236
    wb
    seqf1o.4
    cK
    cM
    cN
    elfzp1
    syl
    mpbid
    mpjaodan
    wph
    @93
    @14
    @10
    wceq
    seqf1o.4
    c.pl
    cG
    cM
    cN
    seqp1
    syl
    3eqtr4d
end
