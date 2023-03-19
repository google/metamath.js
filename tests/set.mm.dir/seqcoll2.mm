include "chash.mm"
include "cfv.mm"
include "cseq.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cuz.mm"
include "fzssuz.mm"
include "wf1o.mm"
include "wf.mm"
include "clt.mm"
include "wiso.mm"
include "isof1o.mm"
include "syl.mm"
include "f1of.mm"
include "wcel.mm"
include "cn.mm"
include "cc0.mm"
include "wceq.mm"
include "wn.mm"
include "c0.mm"
include "wne.mm"
include "cfn.mm"
include "wb.mm"
include "wss.mm"
include "fzfi.mm"
include "ssfi.mm"
include "sylancr.mm"
include "hasheq0.mm"
include "necon3bbid.mm"
include "mpbird.mm"
include "cn0.mm"
include "wo.mm"
include "hashcl.mm"
include "elnn0.mm"
include "sylib.mm"
include "ord.mm"
include "mt3d.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "eluzfz2.mm"
include "ffvelrnd.mm"
include "sseldd.mm"
include "sseldi.mm"
include "elfzuz3.mm"
include "cv.mm"
include "fzss2.mm"
include "sselda.mm"
include "syldan.mm"
include "seqcl.mm"
include "caddc.mm"
include "cdif.mm"
include "wa.mm"
include "peano2uz.mm"
include "fzss1.mm"
include "wbr.mm"
include "cr.mm"
include "eluzelre.mm"
include "adantr.mm"
include "peano2re.mm"
include "elfzelz.mm"
include "zred.mm"
include "adantl.mm"
include "ltp1d.mm"
include "cle.mm"
include "elfzle1.mm"
include "ltletrd.mm"
include "ccnv.mm"
include "f1ocnv.mm"
include "simprr.mm"
include "elfzle2.mm"
include "cz.mm"
include "nn0red.mm"
include "lenltd.mm"
include "mpbid.mm"
include "isorel.mm"
include "syl12anc.mm"
include "f1ocnvfv2.mm"
include "syl2anc.mm"
include "breq2d.mm"
include "bitrd.mm"
include "mtbid.mm"
include "expr.mm"
include "mt2d.mm"
include "eldifd.mm"
include "seqid2.mm"
include "syl6ss.mm"
include "ssdifd.mm"
include "seqcoll.mm"
include "eqtr3d.mm"

theorem seqcoll2
  let wph: wff ph
  let cA: class A
  let c.pl: class .+
  let cS: class S
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  let cZ: class Z
  assume seqcoll2.1: |- ( ( ph /\ k e. S ) -> ( Z .+ k ) = k )
  assume seqcoll2.1b: |- ( ( ph /\ k e. S ) -> ( k .+ Z ) = k )
  assume seqcoll2.c: |- ( ( ph /\ ( k e. S /\ n e. S ) ) -> ( k .+ n ) e. S )
  assume seqcoll2.a: |- ( ph -> Z e. S )
  assume seqcoll2.2: |- ( ph -> G Isom < , < ( ( 1 ... ( # ` A ) ) , A ) )
  assume seqcoll2.3: |- ( ph -> A =/= (/) )
  assume seqcoll2.5: |- ( ph -> A C_ ( M ... N ) )
  assume seqcoll2.6: |- ( ( ph /\ k e. ( M ... N ) ) -> ( F ` k ) e. S )
  assume seqcoll2.7: |- ( ( ph /\ k e. ( ( M ... N ) \ A ) ) -> ( F ` k ) = Z )
  assume seqcoll2.8: |- ( ( ph /\ n e. ( 1 ... ( # ` A ) ) ) -> ( H ` n ) = ( F ` ( G ` n ) ) )

  disjoint k n
  disjoint A k
  disjoint A n
  disjoint F k
  disjoint F n
  disjoint G k
  disjoint G n
  disjoint H n
  disjoint M k
  disjoint M n
  disjoint k ph
  disjoint n ph
  disjoint N k
  disjoint .+ k
  disjoint .+ n
  disjoint S k
  disjoint S n
  disjoint Z k
  assert |- ( ph -> ( seq M ( .+ , F ) ` N ) = ( seq 1 ( .+ , H ) ` ( # ` A ) ) )

  proof
    wph
    cA
    chash
    cfv
    #
    cG
    cfv
    #
    c.pl
    cF
    cM
    cseq
    #
    cfv
    cN
    @2
    cfv
    @0
    c.pl
    cH
    c1
    cseq
    cfv
    wph
    vk
    c.pl
    cS
    cF
    @1
    cM
    cN
    cZ
    seqcoll2.1b
    wph
    cM
    cN
    cfz
    co
    #
    cM
    cuz
    cfv
    #
    @1
    cM
    cN
    fzssuz
    #
    wph
    cA
    @3
    @1
    seqcoll2.5
    wph
    c1
    @0
    cfz
    co
    #
    cA
    @0
    cG
    wph
    @6
    cA
    cG
    wf1o
    #
    @6
    cA
    cG
    wf
    wph
    @6
    cA
    clt
    clt
    cG
    wiso
    #
    @7
    seqcoll2.2
    @6
    cA
    clt
    clt
    cG
    isof1o
    syl
    #
    @6
    cA
    cG
    f1of
    syl
    wph
    @0
    c1
    cuz
    cfv
    #
    wcel
    @0
    @6
    wcel
    #
    wph
    @0
    cn
    @10
    wph
    @0
    cn
    wcel
    #
    @0
    cc0
    wceq
    #
    wph
    @13
    wn
    cA
    c0
    wne
    seqcoll2.3
    wph
    @13
    cA
    c0
    wph
    cA
    cfn
    wcel
    #
    @13
    cA
    c0
    wceq
    wb
    wph
    @3
    cfn
    wcel
    cA
    @3
    wss
    @14
    cM
    cN
    fzfi
    seqcoll2.5
    @3
    cA
    ssfi
    sylancr
    #
    cA
    cfn
    hasheq0
    syl
    necon3bbid
    mpbird
    wph
    @12
    @13
    wph
    @0
    cn0
    wcel
    #
    @12
    @13
    wo
    wph
    @14
    @16
    @15
    cA
    hashcl
    syl
    #
    @0
    elnn0
    sylib
    ord
    mt3d
    nnuz
    syl6eleq
    c1
    @0
    eluzfz2
    syl
    #
    ffvelrnd
    sseldd
    #
    sseldi
    #
    wph
    @1
    @3
    wcel
    cN
    @1
    cuz
    cfv
    wcel
    #
    @19
    @1
    cM
    cN
    elfzuz3
    syl
    #
    wph
    vk
    vn
    c.pl
    cS
    cF
    cM
    @1
    @20
    wph
    vk
    cv
    #
    cM
    @1
    cfz
    co
    #
    wcel
    @23
    @3
    wcel
    @23
    cF
    cfv
    #
    cS
    wcel
    wph
    @24
    @3
    @23
    wph
    @21
    @24
    @3
    wss
    @22
    @1
    cM
    cN
    fzss2
    syl
    #
    sselda
    seqcoll2.6
    syldan
    #
    seqcoll2.c
    seqcl
    wph
    @23
    @1
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
    @23
    @3
    cA
    cdif
    #
    wcel
    #
    @25
    cZ
    wceq
    #
    wph
    @30
    wa
    #
    @23
    @3
    cA
    wph
    @29
    @3
    @23
    wph
    @28
    @4
    wcel
    #
    @29
    @3
    wss
    wph
    @1
    @4
    wcel
    #
    @35
    @20
    cM
    @1
    peano2uz
    syl
    @28
    cM
    cN
    fzss1
    syl
    sselda
    @34
    @23
    cA
    wcel
    #
    @1
    @23
    clt
    wbr
    #
    @34
    @1
    @28
    @23
    wph
    @1
    cr
    wcel
    #
    @30
    wph
    @36
    @39
    @20
    cM
    @1
    eluzelre
    syl
    adantr
    #
    @34
    @39
    @28
    cr
    wcel
    @40
    @1
    peano2re
    syl
    @30
    @23
    cr
    wcel
    wph
    @30
    @23
    @23
    @28
    cN
    elfzelz
    zred
    adantl
    @34
    @1
    @40
    ltp1d
    @30
    @28
    @23
    cle
    wbr
    wph
    @23
    @28
    cN
    elfzle1
    adantl
    ltletrd
    wph
    @30
    @37
    @38
    wn
    wph
    @30
    @37
    wa
    #
    wa
    #
    @0
    @23
    cG
    ccnv
    #
    cfv
    #
    clt
    wbr
    #
    @38
    @42
    @44
    @0
    cle
    wbr
    #
    @45
    wn
    @42
    @44
    @6
    wcel
    #
    @46
    @42
    cA
    @6
    @23
    @43
    @42
    cA
    @6
    @43
    wf1o
    #
    cA
    @6
    @43
    wf
    @42
    @7
    @48
    wph
    @7
    @41
    @9
    adantr
    #
    @6
    cA
    cG
    f1ocnv
    syl
    cA
    @6
    @43
    f1of
    syl
    wph
    @30
    @37
    simprr
    #
    ffvelrnd
    #
    @44
    c1
    @0
    elfzle2
    syl
    @42
    @44
    @0
    @42
    @44
    @42
    @47
    @44
    cz
    wcel
    @51
    @44
    c1
    @0
    elfzelz
    syl
    zred
    @42
    @0
    wph
    @16
    @41
    @17
    adantr
    nn0red
    lenltd
    mpbid
    @42
    @45
    @1
    @44
    cG
    cfv
    #
    clt
    wbr
    #
    @38
    @42
    @8
    @11
    @47
    @45
    @53
    wb
    wph
    @8
    @41
    seqcoll2.2
    adantr
    wph
    @11
    @41
    @18
    adantr
    @51
    @6
    cA
    @0
    @44
    clt
    clt
    cG
    isorel
    syl12anc
    @42
    @52
    @23
    @1
    clt
    @42
    @7
    @37
    @52
    @23
    wceq
    @49
    @50
    @6
    cA
    @23
    cG
    f1ocnvfv2
    syl2anc
    breq2d
    bitrd
    mtbid
    expr
    mt2d
    eldifd
    seqcoll2.7
    syldan
    seqid2
    wph
    cA
    c.pl
    cS
    vk
    vn
    cF
    cG
    cH
    cM
    @0
    cZ
    seqcoll2.1
    seqcoll2.1b
    seqcoll2.c
    seqcoll2.a
    seqcoll2.2
    @18
    wph
    cA
    @3
    @4
    seqcoll2.5
    @5
    syl6ss
    @27
    wph
    @23
    @24
    cA
    cdif
    #
    wcel
    @32
    @33
    wph
    @54
    @31
    @23
    wph
    @24
    @3
    cA
    @26
    ssdifd
    sselda
    seqcoll2.7
    syldan
    seqcoll2.8
    seqcoll
    eqtr3d
end
