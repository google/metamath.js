include "cdif.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "wa.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "cif.mm"
include "ballotlemsv.mm"
include "cz.mm"
include "wss.mm"
include "cuz.mm"
include "fzssuz.mm"
include "uzssz.mm"
include "sstri.mm"
include "cc0.mm"
include "wceq.mm"
include "ballotlemiex.mm"
include "simpld.mm"
include "sseldi.mm"
include "ad2antrr.mm"
include "cn.mm"
include "nnaddcl.mm"
include "mp2an.mm"
include "nnzi.mm"
include "a1i.mm"
include "elfzle2.mm"
include "syl.mm"
include "w3a.mm"
include "eluz2.mm"
include "fzss2.mm"
include "sylbir.mm"
include "syl3anc.mm"
include "1zzd.mm"
include "simplr.mm"
include "elfzle1.mm"
include "simpr.mm"
include "elfz4.mm"
include "syl32anc.mm"
include "fzrev3i.mm"
include "wb.mm"
include "1cnd.mm"
include "zcnd.mm"
include "addcomd.mm"
include "oveq1d.mm"
include "eleq1d.mm"
include "mpbid.mm"
include "sseldd.mm"
include "wn.mm"
include "ifclda.mm"
include "eqeltrd.mm"

theorem ballotlemsdom
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
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint F j
  disjoint c d
  disjoint d k
  assert |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( M + N ) ) ) -> ( ( S ` C ) ` J ) e. ( 1 ... ( M + N ) ) )

  proof
    cC
    cO
    cE
    cdif
    wcel
    #
    cJ
    c1
    cM
    cN
    caddc
    co
    #
    cfz
    co
    #
    wcel
    #
    wa
    #
    cJ
    cC
    cS
    cfv
    cfv
    cJ
    cC
    cI
    cfv
    #
    cle
    wbr
    #
    @5
    c1
    caddc
    co
    #
    cJ
    cmin
    co
    #
    cJ
    cif
    @2
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
    @4
    @6
    @8
    cJ
    @2
    @4
    @6
    wa
    #
    c1
    @5
    cfz
    co
    #
    @2
    @8
    @9
    @5
    cz
    wcel
    #
    @1
    cz
    wcel
    #
    @5
    @1
    cle
    wbr
    #
    @10
    @2
    wss
    #
    @0
    @11
    @3
    @6
    @0
    @2
    cz
    @5
    @2
    c1
    cuz
    cfv
    cz
    c1
    @1
    fzssuz
    c1
    uzssz
    sstri
    #
    @0
    @5
    @2
    wcel
    #
    @5
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
    sseldi
    #
    ad2antrr
    #
    @12
    @9
    @1
    cM
    cn
    wcel
    cN
    cn
    wcel
    @1
    cn
    wcel
    ballotth.m
    ballotth.n
    cM
    cN
    nnaddcl
    mp2an
    nnzi
    a1i
    @9
    @16
    @13
    @0
    @16
    @3
    @6
    @17
    ad2antrr
    @5
    c1
    @1
    elfzle2
    syl
    @11
    @12
    @13
    w3a
    @1
    @5
    cuz
    cfv
    wcel
    @14
    @5
    @1
    eluz2
    @5
    c1
    @1
    fzss2
    sylbir
    syl3anc
    @9
    c1
    @5
    caddc
    co
    #
    cJ
    cmin
    co
    #
    @10
    wcel
    #
    @8
    @10
    wcel
    #
    @9
    cJ
    @10
    wcel
    #
    @22
    @9
    c1
    cz
    wcel
    @11
    cJ
    cz
    wcel
    c1
    cJ
    cle
    wbr
    #
    @6
    @24
    @9
    1zzd
    @19
    @9
    @2
    cz
    cJ
    @15
    @0
    @3
    @6
    simplr
    #
    sseldi
    @9
    @3
    @25
    @26
    cJ
    c1
    @1
    elfzle1
    syl
    @4
    @6
    simpr
    cJ
    c1
    @5
    elfz4
    syl32anc
    cJ
    c1
    @5
    fzrev3i
    syl
    @0
    @22
    @23
    wb
    @3
    @6
    @0
    @21
    @8
    @10
    @0
    @20
    @7
    cJ
    cmin
    @0
    c1
    @5
    @0
    1cnd
    @0
    @5
    @18
    zcnd
    addcomd
    oveq1d
    eleq1d
    ad2antrr
    mpbid
    sseldd
    @0
    @3
    @6
    wn
    simplr
    ifclda
    eqeltrd
end
