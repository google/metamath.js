include "cfz.mm"
include "co.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "cif.mm"
include "cfv.mm"
include "ccnv.mm"
include "cmin.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "fvexd.mm"
include "fvex.mm"
include "ovex.mm"
include "ifex.mm"
include "a1i.mm"
include "wceq.mm"
include "wi.mm"
include "wb.mm"
include "iftrue.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "adantl.mm"
include "simprr.mm"
include "wne.mm"
include "cr.mm"
include "elfzelz.mm"
include "zred.mm"
include "ad2antlr.mm"
include "simprl.mm"
include "gtned.mm"
include "wn.mm"
include "wo.mm"
include "wf.mm"
include "wf1o.mm"
include "f1of.mm"
include "syl.mm"
include "ad2antrr.mm"
include "fzssp1.mm"
include "simplr.mm"
include "sseldi.mm"
include "ffvelrnd.mm"
include "cuz.mm"
include "elfzp1.mm"
include "mpbid.mm"
include "ord.mm"
include "f1ocnvfv.mm"
include "syl2anc.mm"
include "eqeq1i.mm"
include "syl6ibr.mm"
include "syld.mm"
include "necon1ad.mm"
include "mpd.mm"
include "eqeltrd.mm"
include "eqcomd.mm"
include "eqbrtrd.mm"
include "eqtr2d.mm"
include "jca.mm"
include "expr.mm"
include "sylbid.mm"
include "iffalse.mm"
include "cz.mm"
include "wf1.mm"
include "f1ocnv.mm"
include "f1of1.mm"
include "f1f.mm"
include "peano2uz.mm"
include "eluzfz2.mm"
include "syl5eqel.mm"
include "peano2re.mm"
include "cle.mm"
include "lenltd.mm"
include "mpbird.mm"
include "ltp1d.mm"
include "lelttrd.mm"
include "ltned.mm"
include "fzp1elp1.mm"
include "breq1d.mm"
include "lttr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "mtod.mm"
include "oveq1d.mm"
include "cc.mm"
include "recnd.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "3eqtrrd.mm"
include "pm2.61dan.mm"
include "expimpd.mm"
include "elfzle1.mm"
include "eluzelz.mm"
include "peano2zd.mm"
include "elfzle2.mm"
include "ltletrd.mm"
include "zleltp1.mm"
include "eluzel2.mm"
include "elfz.mm"
include "mpbir2and.mm"
include "f1ocnvfv2.mm"
include "peano2zm.mm"
include "adantr.mm"
include "f1fveq.mm"
include "syl12anc.mm"
include "necon3bid.mm"
include "neeq1i.mm"
include "sylibr.mm"
include "necomd.mm"
include "ltlend.mm"
include "zltlem1.mm"
include "breqtrrd.mm"
include "letrd.mm"
include "1re.mm"
include "lesubadd.mm"
include "mp3an2.mm"
include "zcnd.mm"
include "npcan.mm"
include "eqtrd.mm"
include "impbid.mm"
include "f1od.mm"

theorem seqf1olem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let c.pl: class .+
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let vf: setvar f
  let vg: setvar g
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
  disjoint G k
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint M k
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint .+ k
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint N k
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint K k
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint S k
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint C k
  disjoint C x
  disjoint C y
  disjoint C z
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
  disjoint f m
  disjoint f n
  disjoint G f
  disjoint g m
  disjoint g n
  disjoint G g
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
  disjoint M f
  disjoint g s
  disjoint g t
  disjoint g w
  disjoint M g
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
  disjoint .+ f
  disjoint .+ g
  disjoint .+ m
  disjoint .+ n
  disjoint .+ s
  disjoint .+ t
  disjoint .+ w
  disjoint J f
  disjoint J g
  disjoint N f
  disjoint N g
  disjoint N m
  disjoint N n
  disjoint K m
  disjoint K n
  disjoint f ph
  disjoint g ph
  disjoint m ph
  disjoint n ph
  disjoint ph s
  disjoint ph t
  disjoint ph w
  disjoint S s
  disjoint S t
  disjoint S w
  disjoint C f
  disjoint C g
  disjoint C s
  disjoint C t
  disjoint C w
  disjoint H k
  assert |- ( ph -> J : ( M ... N ) -1-1-onto-> ( M ... N ) )

  proof
    wph
    vk
    vx
    cM
    cN
    cfz
    co
    #
    @0
    vk
    cv
    #
    cK
    clt
    wbr
    #
    @1
    @1
    c1
    caddc
    co
    #
    cif
    #
    cF
    cfv
    #
    vx
    cv
    #
    cF
    ccnv
    #
    cfv
    #
    cK
    clt
    wbr
    #
    @8
    @8
    c1
    cmin
    co
    #
    cif
    #
    cJ
    cvv
    cvv
    seqf1olem.7
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @4
    cF
    fvexd
    @11
    cvv
    wcel
    wph
    @6
    @0
    wcel
    #
    wa
    #
    @9
    @8
    @10
    @6
    @7
    fvex
    @8
    c1
    cmin
    ovex
    ifex
    a1i
    wph
    @12
    @6
    @5
    wceq
    #
    wa
    #
    @14
    @1
    @11
    wceq
    #
    wa
    #
    wph
    @12
    @16
    @19
    @13
    @2
    @16
    @19
    wi
    @13
    @2
    wa
    @16
    @6
    @1
    cF
    cfv
    #
    wceq
    #
    @19
    @2
    @16
    @21
    wb
    @13
    @2
    @5
    @20
    @6
    @2
    @4
    @1
    cF
    @2
    @1
    @3
    iftrue
    fveq2d
    #
    eqeq2d
    adantl
    @13
    @2
    @21
    @19
    @13
    @2
    @21
    wa
    #
    wa
    #
    @14
    @18
    @24
    @6
    @20
    @0
    @13
    @2
    @21
    simprr
    #
    @24
    cK
    @1
    wne
    @20
    @0
    wcel
    #
    @24
    @1
    cK
    @12
    @1
    cr
    wcel
    #
    wph
    @23
    @12
    @1
    @1
    cM
    cN
    elfzelz
    zred
    #
    ad2antlr
    @13
    @2
    @21
    simprl
    #
    gtned
    @24
    @26
    cK
    @1
    @24
    @26
    wn
    @20
    cN
    c1
    caddc
    co
    #
    wceq
    #
    cK
    @1
    wceq
    #
    @24
    @26
    @31
    @24
    @20
    cM
    @30
    cfz
    co
    #
    wcel
    #
    @26
    @31
    wo
    #
    @24
    @33
    @33
    @1
    cF
    wph
    @33
    @33
    cF
    wf
    #
    @12
    @23
    wph
    @33
    @33
    cF
    wf1o
    #
    @36
    seqf1olem.5
    @33
    @33
    cF
    f1of
    syl
    #
    ad2antrr
    @24
    @0
    @33
    @1
    cM
    cN
    fzssp1
    #
    wph
    @12
    @23
    simplr
    sseldi
    #
    ffvelrnd
    wph
    @34
    @35
    wb
    #
    @12
    @23
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    @41
    seqf1o.4
    @20
    cM
    cN
    elfzp1
    syl
    ad2antrr
    mpbid
    ord
    @24
    @31
    @30
    @7
    cfv
    #
    @1
    wceq
    #
    @32
    @24
    @37
    @1
    @33
    wcel
    #
    @31
    @45
    wi
    wph
    @37
    @12
    @23
    seqf1olem.5
    ad2antrr
    #
    @40
    @33
    @33
    @1
    @30
    cF
    f1ocnvfv
    syl2anc
    cK
    @44
    @1
    seqf1olem.8
    eqeq1i
    syl6ibr
    syld
    necon1ad
    mpd
    eqeltrd
    @24
    @11
    @8
    @1
    @24
    @9
    @11
    @8
    wceq
    @24
    @8
    @1
    cK
    clt
    @24
    @20
    @6
    wceq
    #
    @8
    @1
    wceq
    #
    @24
    @6
    @20
    @25
    eqcomd
    @24
    @37
    @46
    @48
    @49
    wi
    @47
    @40
    @33
    @33
    @1
    @6
    cF
    f1ocnvfv
    syl2anc
    mpd
    #
    @29
    eqbrtrd
    @9
    @8
    @10
    iftrue
    #
    syl
    @50
    eqtr2d
    jca
    expr
    sylbid
    @13
    @2
    wn
    #
    wa
    @16
    @6
    @3
    cF
    cfv
    #
    wceq
    #
    @19
    @52
    @16
    @54
    wb
    @13
    @52
    @5
    @53
    @6
    @52
    @4
    @3
    cF
    @2
    @1
    @3
    iffalse
    fveq2d
    #
    eqeq2d
    adantl
    @13
    @52
    @54
    @19
    @13
    @52
    @54
    wa
    #
    wa
    #
    @14
    @18
    @57
    @6
    @53
    @0
    @13
    @52
    @54
    simprr
    #
    @57
    cK
    @3
    wne
    @53
    @0
    wcel
    #
    @57
    cK
    @3
    wph
    cK
    cr
    wcel
    #
    @12
    @56
    wph
    cK
    wph
    cK
    @33
    wcel
    #
    cK
    cz
    wcel
    #
    wph
    cK
    @44
    @33
    seqf1olem.8
    wph
    @33
    @33
    @30
    @7
    wph
    @33
    @33
    @7
    wf1
    #
    @33
    @33
    @7
    wf
    #
    wph
    @33
    @33
    @7
    wf1o
    #
    @63
    wph
    @37
    @65
    seqf1olem.5
    @33
    @33
    cF
    f1ocnv
    syl
    @33
    @33
    @7
    f1of1
    syl
    #
    @33
    @33
    @7
    f1f
    syl
    #
    wph
    @30
    @42
    wcel
    #
    @30
    @33
    wcel
    #
    wph
    @43
    @68
    seqf1o.4
    cM
    cN
    peano2uz
    syl
    cM
    @30
    eluzfz2
    syl
    #
    ffvelrnd
    syl5eqel
    #
    cK
    cM
    @30
    elfzelz
    syl
    #
    zred
    #
    ad2antrr
    #
    @57
    cK
    @1
    @3
    @74
    @12
    @27
    wph
    @56
    @28
    ad2antlr
    #
    @57
    @27
    @3
    cr
    wcel
    #
    @75
    @1
    peano2re
    syl
    #
    @57
    cK
    @1
    cle
    wbr
    #
    @52
    @13
    @52
    @54
    simprl
    #
    @57
    cK
    @1
    @74
    @75
    lenltd
    mpbird
    @57
    @1
    @75
    ltp1d
    #
    lelttrd
    ltned
    @57
    @59
    cK
    @3
    @57
    @59
    wn
    @53
    @30
    wceq
    #
    cK
    @3
    wceq
    #
    @57
    @59
    @81
    @57
    @53
    @33
    wcel
    #
    @59
    @81
    wo
    #
    @57
    @33
    @33
    @3
    cF
    wph
    @36
    @12
    @56
    @38
    ad2antrr
    @12
    @3
    @33
    wcel
    #
    wph
    @56
    @1
    cM
    cN
    fzp1elp1
    ad2antlr
    #
    ffvelrnd
    wph
    @83
    @84
    wb
    #
    @12
    @56
    wph
    @43
    @87
    seqf1o.4
    @53
    cM
    cN
    elfzp1
    syl
    ad2antrr
    mpbid
    ord
    @57
    @81
    @44
    @3
    wceq
    #
    @82
    @57
    @37
    @85
    @81
    @88
    wi
    wph
    @37
    @12
    @56
    seqf1olem.5
    ad2antrr
    #
    @86
    @33
    @33
    @3
    @30
    cF
    f1ocnvfv
    syl2anc
    cK
    @44
    @3
    seqf1olem.8
    eqeq1i
    syl6ibr
    syld
    necon1ad
    mpd
    eqeltrd
    @57
    @11
    @10
    @3
    c1
    cmin
    co
    #
    @1
    @57
    @9
    wn
    #
    @11
    @10
    wceq
    @57
    @9
    @2
    @79
    @57
    @9
    @3
    cK
    clt
    wbr
    #
    @2
    @57
    @8
    @3
    cK
    clt
    @57
    @53
    @6
    wceq
    #
    @8
    @3
    wceq
    #
    @57
    @6
    @53
    @58
    eqcomd
    @57
    @37
    @85
    @93
    @94
    wi
    @89
    @86
    @33
    @33
    @3
    @6
    cF
    f1ocnvfv
    syl2anc
    mpd
    #
    breq1d
    @57
    @1
    @3
    clt
    wbr
    #
    @92
    @2
    @80
    @57
    @27
    @76
    @60
    @96
    @92
    wa
    @2
    wi
    @75
    @77
    @74
    @1
    @3
    cK
    lttr
    syl3anc
    mpand
    sylbid
    mtod
    @9
    @8
    @10
    iffalse
    #
    syl
    @57
    @8
    @3
    c1
    cmin
    @95
    oveq1d
    @57
    @1
    cc
    wcel
    c1
    cc
    wcel
    #
    @90
    @1
    wceq
    @57
    @1
    @75
    recnd
    ax-1cn
    @1
    c1
    pncan
    sylancl
    3eqtrrd
    jca
    expr
    sylbid
    pm2.61dan
    expimpd
    wph
    @14
    @18
    @17
    @15
    @9
    @18
    @17
    wi
    @15
    @9
    wa
    @18
    @1
    @8
    wceq
    #
    @17
    @9
    @18
    @99
    wb
    @15
    @9
    @11
    @8
    @1
    @51
    eqeq2d
    adantl
    @15
    @9
    @99
    @17
    @15
    @9
    @99
    wa
    #
    wa
    #
    @12
    @16
    @101
    @12
    cM
    @1
    cle
    wbr
    #
    @1
    cN
    cle
    wbr
    #
    @101
    @46
    @102
    @101
    @1
    @8
    @33
    @15
    @9
    @99
    simprr
    #
    @101
    @33
    @33
    @6
    @7
    wph
    @64
    @14
    @100
    @67
    ad2antrr
    @101
    @0
    @33
    @6
    @39
    wph
    @14
    @100
    simplr
    sseldi
    #
    ffvelrnd
    eqeltrd
    #
    @1
    cM
    @30
    elfzle1
    syl
    @101
    @103
    @1
    @30
    clt
    wbr
    #
    @101
    @1
    cK
    @30
    @101
    @1
    @101
    @46
    @1
    cz
    wcel
    #
    @106
    @1
    cM
    @30
    elfzelz
    syl
    #
    zred
    wph
    @60
    @14
    @100
    @73
    ad2antrr
    wph
    @30
    cr
    wcel
    #
    @14
    @100
    wph
    @30
    wph
    cN
    wph
    @43
    cN
    cz
    wcel
    #
    seqf1o.4
    cM
    cN
    eluzelz
    syl
    #
    peano2zd
    zred
    #
    ad2antrr
    @101
    @1
    @8
    cK
    clt
    @104
    @15
    @9
    @99
    simprl
    eqbrtrd
    #
    wph
    cK
    @30
    cle
    wbr
    #
    @14
    @100
    wph
    @61
    @115
    @71
    cK
    cM
    @30
    elfzle2
    syl
    ad2antrr
    ltletrd
    @101
    @108
    @111
    @103
    @107
    wb
    @109
    wph
    @111
    @14
    @100
    @112
    ad2antrr
    #
    @1
    cN
    zleltp1
    syl2anc
    mpbird
    @101
    @108
    cM
    cz
    wcel
    #
    @111
    @12
    @102
    @103
    wa
    wb
    #
    @109
    wph
    @117
    @14
    @100
    wph
    @43
    @117
    seqf1o.4
    cM
    cN
    eluzel2
    syl
    #
    ad2antrr
    @116
    @1
    cM
    cN
    elfz
    #
    syl3anc
    mpbir2and
    @101
    @5
    @20
    @8
    cF
    cfv
    #
    @6
    @101
    @2
    @5
    @20
    wceq
    @114
    @22
    syl
    @101
    @1
    @8
    cF
    @104
    fveq2d
    @101
    @37
    @6
    @33
    wcel
    #
    @121
    @6
    wceq
    #
    wph
    @37
    @14
    @100
    seqf1olem.5
    ad2antrr
    @105
    @33
    @33
    @6
    cF
    f1ocnvfv2
    #
    syl2anc
    3eqtrrd
    jca
    expr
    sylbid
    @15
    @91
    wa
    @18
    @1
    @10
    wceq
    #
    @17
    @91
    @18
    @125
    wb
    @15
    @91
    @11
    @10
    @1
    @97
    eqeq2d
    adantl
    @15
    @91
    @125
    @17
    @15
    @91
    @125
    wa
    #
    wa
    #
    @12
    @16
    @127
    @12
    @102
    @103
    @127
    cM
    cK
    @1
    wph
    cM
    cr
    wcel
    @14
    @126
    wph
    cM
    @119
    zred
    ad2antrr
    wph
    @60
    @14
    @126
    @73
    ad2antrr
    #
    @127
    @1
    @127
    @1
    @10
    cz
    @15
    @91
    @125
    simprr
    #
    @127
    @8
    cz
    wcel
    #
    @10
    cz
    wcel
    @127
    @8
    @33
    wcel
    #
    @130
    @127
    @33
    @33
    @6
    @7
    wph
    @64
    @14
    @126
    @67
    ad2antrr
    @127
    @0
    @33
    @6
    @39
    wph
    @14
    @126
    simplr
    sseldi
    #
    ffvelrnd
    #
    @8
    cM
    @30
    elfzelz
    syl
    #
    @8
    peano2zm
    syl
    eqeltrd
    #
    zred
    #
    wph
    cM
    cK
    cle
    wbr
    #
    @14
    @126
    wph
    @61
    @137
    @71
    cK
    cM
    @30
    elfzle1
    syl
    ad2antrr
    @127
    cK
    @10
    @1
    cle
    @127
    cK
    @8
    clt
    wbr
    #
    cK
    @10
    cle
    wbr
    #
    @127
    @138
    cK
    @8
    cle
    wbr
    #
    @8
    cK
    wne
    @127
    @140
    @91
    @15
    @91
    @125
    simprl
    @127
    cK
    @8
    @128
    @127
    @8
    @134
    zred
    #
    lenltd
    mpbird
    @127
    cK
    @8
    @127
    @44
    @8
    wne
    #
    cK
    @8
    wne
    @127
    @142
    @30
    @6
    wne
    #
    @15
    @143
    @126
    @15
    @6
    @30
    @15
    @6
    @14
    @6
    cz
    wcel
    wph
    @6
    cM
    cN
    elfzelz
    adantl
    zred
    #
    @15
    @6
    cN
    @30
    @144
    wph
    cN
    cr
    wcel
    #
    @14
    wph
    cN
    @112
    zred
    #
    adantr
    #
    wph
    @110
    @14
    @113
    adantr
    @14
    @6
    cN
    cle
    wbr
    wph
    @6
    cM
    cN
    elfzle2
    adantl
    @15
    cN
    @147
    ltp1d
    lelttrd
    gtned
    adantr
    @127
    @44
    @8
    @30
    @6
    @127
    @63
    @69
    @122
    @44
    @8
    wceq
    @30
    @6
    wceq
    wb
    wph
    @63
    @14
    @126
    @66
    ad2antrr
    wph
    @69
    @14
    @126
    @70
    ad2antrr
    @132
    @33
    @33
    @30
    @6
    @7
    f1fveq
    syl12anc
    necon3bid
    mpbird
    cK
    @44
    @8
    seqf1olem.8
    neeq1i
    sylibr
    necomd
    @127
    cK
    @8
    @128
    @141
    ltlend
    mpbir2and
    @127
    @62
    @130
    @138
    @139
    wb
    wph
    @62
    @14
    @126
    @72
    ad2antrr
    @134
    cK
    @8
    zltlem1
    syl2anc
    mpbid
    @129
    breqtrrd
    #
    letrd
    @127
    @1
    @10
    cN
    cle
    @129
    @127
    @10
    cN
    cle
    wbr
    #
    @8
    @30
    cle
    wbr
    #
    @127
    @131
    @150
    @133
    @8
    cM
    @30
    elfzle2
    syl
    @127
    @8
    cr
    wcel
    #
    @145
    @149
    @150
    wb
    #
    @141
    wph
    @145
    @14
    @126
    @146
    ad2antrr
    @151
    c1
    cr
    wcel
    @145
    @152
    1re
    @8
    c1
    cN
    lesubadd
    mp3an2
    syl2anc
    mpbird
    eqbrtrd
    @127
    @108
    @117
    @111
    @118
    @135
    wph
    @117
    @14
    @126
    @119
    ad2antrr
    wph
    @111
    @14
    @126
    @112
    ad2antrr
    @120
    syl3anc
    mpbir2and
    @127
    @5
    @53
    @121
    @6
    @127
    @52
    @5
    @53
    wceq
    @127
    @78
    @52
    @148
    @127
    cK
    @1
    @128
    @136
    lenltd
    mpbid
    @55
    syl
    @127
    @3
    @8
    cF
    @127
    @3
    @10
    c1
    caddc
    co
    #
    @8
    @127
    @1
    @10
    c1
    caddc
    @129
    oveq1d
    @127
    @8
    cc
    wcel
    @98
    @153
    @8
    wceq
    @127
    @8
    @134
    zcnd
    ax-1cn
    @8
    c1
    npcan
    sylancl
    eqtrd
    fveq2d
    @127
    @37
    @122
    @123
    wph
    @37
    @14
    @126
    seqf1olem.5
    ad2antrr
    @132
    @124
    syl2anc
    3eqtrrd
    jca
    expr
    sylbid
    pm2.61dan
    expimpd
    impbid
    f1od
end
