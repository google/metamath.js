include "cdif.mm"
include "wcel.mm"
include "c1.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cima.mm"
include "cz.mm"
include "cv.mm"
include "wss.mm"
include "caddc.mm"
include "crn.mm"
include "imassrn.mm"
include "wf1o.mm"
include "wf.mm"
include "ccnv.mm"
include "wceq.mm"
include "ballotlemsf1o.mm"
include "simpld.mm"
include "f1of.mm"
include "frn.mm"
include "3syl.mm"
include "syl5ss.mm"
include "cuz.mm"
include "fzssuz.mm"
include "uzssz.mm"
include "sstri.mm"
include "syl6ss.mm"
include "adantr.mm"
include "sselda.mm"
include "elfzelz.mm"
include "adantl.mm"
include "wrex.mm"
include "wb.mm"
include "wfn.mm"
include "f1ofn.mm"
include "syl.mm"
include "cc0.mm"
include "ballotlemiex.mm"
include "elfzuz3.mm"
include "uztrn.mm"
include "syl2anc.mm"
include "fzss2.mm"
include "fvelimab.mm"
include "cmin.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "1zzd.mm"
include "nnzi.mm"
include "zaddcl.mm"
include "mp2an.mm"
include "a1i.mm"
include "elfzle1.mm"
include "zred.mm"
include "elfzle2.mm"
include "letrd.mm"
include "elfz4.mm"
include "syl32anc.mm"
include "ballotlemsv.mm"
include "syldan.mm"
include "simpr.mm"
include "iftrue.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "eleq2d.mm"
include "ad2antrr.mm"
include "zcnd.mm"
include "1cnd.mm"
include "pncand.mm"
include "oveq2d.mm"
include "ad2antlr.mm"
include "peano2zd.mm"
include "fzrev.mm"
include "syl22anc.mm"
include "3bitr2d.mm"
include "risset.mm"
include "eqcom.mm"
include "cc.mm"
include "adantlr.mm"
include "addcld.mm"
include "simplr.mm"
include "subsub23.mm"
include "syl3anc.mm"
include "syl5bbr.mm"
include "simpll.mm"
include "eqeq1d.mm"
include "bitr4d.mm"
include "rexbidva.mm"
include "3bitrd.mm"
include "eqrdav.mm"

theorem ballotlemsima
  let vx: setvar x
  let cC: class C
  let cP: class P
  let cS: class S
  let vi: setvar i
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cI: class I
  let cJ: class J
  let cM: class M
  let cN: class N
  let cO: class O
  let vc: setvar c
  let vj: setvar j
  let vd: setvar d
  assume ballotth.m: |- M e. NN
  assume ballotth.n: |- N e. NN
  assume ballotth.o: |- O = { c e. ~P ( 1 ... ( M + N ) ) | ( # ` c ) = M }
  assume ballotth.p: |- P = ( x e. ~P O |-> ( ( # ` x ) / ( # ` O ) ) )
  assume ballotth.f: |- F = ( c e. O |-> ( i e. ZZ |-> ( ( # ` ( ( 1 ... i ) i^i c ) ) - ( # ` ( ( 1 ... i ) \ c ) ) ) ) )
  assume ballotth.e: |- E = { c e. O | A. i e. ( 1 ... ( M + N ) ) 0 < ( ( F ` c ) ` i ) }
  assume ballotth.mgtn: |- N < M
  assume ballotth.i: |- I = ( c e. ( O \ E ) |-> inf ( { k e. ( 1 ... ( M + N ) ) | ( ( F ` c ) ` k ) = 0 } , RR , < ) )
  assume ballotth.s: |- S = ( c e. ( O \ E ) |-> ( i e. ( 1 ... ( M + N ) ) |-> if ( i <_ ( I ` c ) , ( ( ( I ` c ) + 1 ) - i ) , i ) ) )

  disjoint M c
  disjoint N c
  disjoint O c
  disjoint M i
  disjoint N i
  disjoint O i
  disjoint M k
  disjoint N k
  disjoint O k
  disjoint c i
  disjoint F c
  disjoint F i
  disjoint F k
  disjoint C i
  disjoint i k
  disjoint E i
  disjoint E k
  disjoint C k
  disjoint I k
  disjoint c k
  disjoint E c
  disjoint I i
  disjoint I c
  disjoint J k
  disjoint S k
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint F j
  disjoint c d
  disjoint d k
  disjoint i j
  disjoint I j
  disjoint C j
  disjoint E j
  disjoint J j
  disjoint j k
  disjoint S j
  assert |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( I ` C ) ) ) -> ( ( S ` C ) " ( 1 ... J ) ) = ( ( ( S ` C ) ` J ) ... ( I ` C ) ) )

  proof
    cC
    cO
    cE
    cdif
    wcel
    #
    cJ
    c1
    cC
    cI
    cfv
    #
    cfz
    co
    wcel
    #
    wa
    #
    vk
    cC
    cS
    cfv
    #
    c1
    cJ
    cfz
    co
    #
    cima
    #
    cJ
    @4
    cfv
    #
    @1
    cfz
    co
    #
    cz
    @3
    @6
    cz
    vk
    cv
    #
    @0
    @6
    cz
    wss
    @2
    @0
    @6
    c1
    cM
    cN
    caddc
    co
    #
    cfz
    co
    #
    cz
    @0
    @6
    @4
    crn
    #
    @11
    @4
    @5
    imassrn
    @0
    @11
    @11
    @4
    wf1o
    #
    @11
    @11
    @4
    wf
    @12
    @11
    wss
    @0
    @13
    @4
    ccnv
    @4
    wceq
    vx
    cC
    cP
    cS
    vi
    vk
    cE
    cF
    cI
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    ballotth.e
    ballotth.mgtn
    ballotth.i
    ballotth.s
    ballotlemsf1o
    simpld
    #
    @11
    @11
    @4
    f1of
    @11
    @11
    @4
    frn
    3syl
    syl5ss
    @11
    c1
    cuz
    cfv
    cz
    c1
    @10
    fzssuz
    c1
    uzssz
    sstri
    syl6ss
    adantr
    sselda
    @9
    @8
    wcel
    #
    @9
    cz
    wcel
    #
    @3
    @9
    @7
    @1
    elfzelz
    adantl
    @3
    @16
    wa
    #
    @9
    @6
    wcel
    #
    vj
    cv
    #
    @4
    cfv
    #
    @9
    wceq
    #
    vj
    @5
    wrex
    #
    @15
    @3
    @18
    @22
    wb
    #
    @16
    @3
    @4
    @11
    wfn
    #
    @5
    @11
    wss
    #
    @23
    @0
    @24
    @2
    @0
    @13
    @24
    @14
    @11
    @11
    @4
    f1ofn
    syl
    adantr
    @3
    @10
    cJ
    cuz
    cfv
    #
    wcel
    #
    @25
    @3
    @10
    @1
    cuz
    cfv
    wcel
    #
    @1
    @26
    wcel
    #
    @27
    @3
    @1
    @11
    wcel
    #
    @28
    @0
    @30
    @2
    @0
    @30
    @1
    cC
    cF
    cfv
    cfv
    cc0
    wceq
    vx
    cC
    cP
    vi
    vk
    cE
    cF
    cI
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    ballotth.e
    ballotth.mgtn
    ballotth.i
    ballotlemiex
    simpld
    #
    adantr
    @1
    c1
    @10
    elfzuz3
    syl
    @2
    @29
    @0
    cJ
    c1
    @1
    elfzuz3
    adantl
    @1
    @10
    cJ
    uztrn
    syl2anc
    cJ
    c1
    @10
    fzss2
    syl
    #
    vj
    @11
    @5
    @9
    @4
    fvelimab
    syl2anc
    adantr
    @17
    @15
    @1
    c1
    caddc
    co
    #
    @9
    cmin
    co
    #
    @5
    wcel
    #
    @19
    @34
    wceq
    #
    vj
    @5
    wrex
    #
    @22
    @17
    @15
    @9
    @33
    cJ
    cmin
    co
    #
    @1
    cfz
    co
    #
    wcel
    #
    @9
    @38
    @33
    c1
    cmin
    co
    #
    cfz
    co
    #
    wcel
    #
    @35
    @3
    @15
    @40
    wb
    @16
    @3
    @8
    @39
    @9
    @3
    @7
    @38
    @1
    cfz
    @3
    @7
    cJ
    @1
    cle
    wbr
    #
    @38
    cJ
    cif
    #
    @38
    @0
    @2
    cJ
    @11
    wcel
    #
    @7
    @45
    wceq
    @3
    c1
    cz
    wcel
    #
    @10
    cz
    wcel
    #
    cJ
    cz
    wcel
    #
    c1
    cJ
    cle
    wbr
    #
    cJ
    @10
    cle
    wbr
    @46
    @3
    1zzd
    @48
    @3
    cM
    cz
    wcel
    cN
    cz
    wcel
    @48
    cM
    ballotth.m
    nnzi
    cN
    ballotth.n
    nnzi
    cM
    cN
    zaddcl
    mp2an
    a1i
    #
    @2
    @49
    @0
    cJ
    c1
    @1
    elfzelz
    #
    adantl
    #
    @2
    @50
    @0
    cJ
    c1
    @1
    elfzle1
    adantl
    @3
    cJ
    @1
    @10
    @3
    cJ
    @53
    zred
    @3
    @1
    @0
    @1
    cz
    wcel
    #
    @2
    @0
    @30
    @54
    @31
    @1
    c1
    @10
    elfzelz
    syl
    #
    adantr
    zred
    @3
    @10
    @51
    zred
    @2
    @44
    @0
    cJ
    c1
    @1
    elfzle2
    #
    adantl
    @0
    @1
    @10
    cle
    wbr
    #
    @2
    @0
    @30
    @57
    @31
    @1
    c1
    @10
    elfzle2
    syl
    adantr
    letrd
    cJ
    c1
    @10
    elfz4
    syl32anc
    vx
    cC
    cP
    cS
    vi
    vk
    cE
    cF
    cI
    cJ
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    ballotth.e
    ballotth.mgtn
    ballotth.i
    ballotth.s
    ballotlemsv
    syldan
    @3
    @2
    @44
    @45
    @38
    wceq
    @0
    @2
    simpr
    @56
    @44
    @38
    cJ
    iftrue
    3syl
    eqtrd
    oveq1d
    eleq2d
    adantr
    @17
    @42
    @39
    @9
    @17
    @41
    @1
    @38
    cfz
    @17
    @1
    c1
    @17
    @1
    @0
    @54
    @2
    @16
    @55
    ad2antrr
    #
    zcnd
    @17
    1cnd
    pncand
    oveq2d
    eleq2d
    @17
    @47
    @49
    @33
    cz
    wcel
    @16
    @43
    @35
    wb
    @17
    1zzd
    @2
    @49
    @0
    @16
    @52
    ad2antlr
    @17
    @1
    @58
    peano2zd
    @3
    @16
    simpr
    @33
    @9
    c1
    cJ
    fzrev
    syl22anc
    3bitr2d
    @35
    @37
    wb
    @17
    vj
    @34
    @5
    risset
    a1i
    @17
    @36
    @21
    vj
    @5
    @17
    @19
    @5
    wcel
    #
    wa
    #
    @36
    @33
    @19
    cmin
    co
    #
    @9
    wceq
    #
    @21
    @36
    @34
    @19
    wceq
    #
    @60
    @62
    @34
    @19
    eqcom
    @60
    @33
    cc
    wcel
    @9
    cc
    wcel
    @19
    cc
    wcel
    @63
    @62
    wb
    @60
    @1
    c1
    @60
    @1
    @3
    @59
    @54
    @16
    @0
    @54
    @2
    @59
    @55
    ad2antrr
    #
    adantlr
    zcnd
    @60
    1cnd
    addcld
    @60
    @9
    @3
    @16
    @59
    simplr
    zcnd
    @60
    @19
    @59
    @19
    cz
    wcel
    #
    @17
    @19
    c1
    cJ
    elfzelz
    #
    adantl
    zcnd
    @33
    @9
    @19
    subsub23
    syl3anc
    syl5bbr
    @3
    @59
    @21
    @62
    wb
    @16
    @3
    @59
    wa
    #
    @20
    @61
    @9
    @67
    @20
    @19
    @1
    cle
    wbr
    #
    @61
    @19
    cif
    #
    @61
    @67
    @0
    @19
    @11
    wcel
    @20
    @69
    wceq
    @0
    @2
    @59
    simpll
    @3
    @5
    @11
    @19
    @32
    sselda
    vx
    cC
    cP
    cS
    vi
    vk
    cE
    cF
    cI
    @19
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    ballotth.e
    ballotth.mgtn
    ballotth.i
    ballotth.s
    ballotlemsv
    syl2anc
    @67
    @68
    @69
    @61
    wceq
    @67
    @19
    cJ
    @1
    @67
    @19
    @59
    @65
    @3
    @66
    adantl
    zred
    @67
    cJ
    @2
    @49
    @0
    @59
    @52
    ad2antlr
    zred
    @67
    @1
    @64
    zred
    @59
    @19
    cJ
    cle
    wbr
    @3
    @19
    c1
    cJ
    elfzle2
    adantl
    @2
    @44
    @0
    @59
    @56
    ad2antlr
    letrd
    @68
    @61
    @19
    iftrue
    syl
    eqtrd
    eqeq1d
    adantlr
    bitr4d
    rexbidva
    3bitrd
    bitr4d
    eqrdav
end
