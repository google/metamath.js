include "cdif.mm"
include "wcel.mm"
include "c1.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "1zzd.mm"
include "caddc.mm"
include "cc0.mm"
include "wceq.mm"
include "ballotlemiex.mm"
include "simpld.mm"
include "elfzelz.mm"
include "syl.mm"
include "adantr.mm"
include "cuz.mm"
include "wss.mm"
include "cn.mm"
include "nnaddcl.mm"
include "mp2an.mm"
include "nnzi.mm"
include "a1i.mm"
include "elfzle2.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "fzss2.mm"
include "sselda.mm"
include "ballotlemsdom.mm"
include "syldan.mm"
include "cmin.mm"
include "adantl.mm"
include "zred.mm"
include "1red.mm"
include "readdcld.mm"
include "zcnd.mm"
include "1cnd.mm"
include "pncand.mm"
include "breqtrrd.mm"
include "lesubd.mm"
include "cif.mm"
include "ballotlemsv.mm"
include "iftrued.mm"
include "eqtrd.mm"
include "elfznn.mm"
include "ltesubnnd.mm"
include "eqbrtrd.mm"
include "elfz4.mm"
include "syl32anc.mm"

theorem ballotlemsel1i
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
  assert |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( I ` C ) ) ) -> ( ( S ` C ) ` J ) e. ( 1 ... ( I ` C ) ) )

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
    #
    wcel
    #
    wa
    #
    c1
    cz
    wcel
    @1
    cz
    wcel
    #
    cJ
    cC
    cS
    cfv
    cfv
    #
    cz
    wcel
    #
    c1
    @6
    cle
    wbr
    @6
    @1
    cle
    wbr
    @6
    @2
    wcel
    @4
    1zzd
    @0
    @5
    @3
    @0
    @1
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
    @5
    @0
    @10
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
    @1
    c1
    @8
    elfzelz
    syl
    #
    adantr
    #
    @4
    @6
    @9
    wcel
    #
    @7
    @0
    @3
    cJ
    @9
    wcel
    #
    @14
    @0
    @2
    @9
    cJ
    @0
    @8
    @1
    cuz
    cfv
    wcel
    #
    @2
    @9
    wss
    @0
    @5
    @8
    cz
    wcel
    #
    @1
    @8
    cle
    wbr
    #
    @16
    @12
    @17
    @0
    @8
    cM
    cn
    wcel
    cN
    cn
    wcel
    @8
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
    @0
    @10
    @18
    @11
    @1
    c1
    @8
    elfzle2
    syl
    @1
    @8
    eluz2
    syl3anbrc
    @1
    c1
    @8
    fzss2
    syl
    sselda
    #
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
    ballotlemsdom
    syldan
    @6
    c1
    @8
    elfzelz
    syl
    @4
    c1
    @1
    c1
    caddc
    co
    #
    cJ
    cmin
    co
    #
    @6
    cle
    @4
    cJ
    @20
    c1
    @4
    cJ
    @3
    cJ
    cz
    wcel
    @0
    cJ
    c1
    @1
    elfzelz
    adantl
    zred
    @4
    @1
    c1
    @4
    @1
    @13
    zred
    @4
    1red
    #
    readdcld
    @22
    @4
    cJ
    @1
    @20
    c1
    cmin
    co
    cle
    @3
    cJ
    @1
    cle
    wbr
    #
    @0
    cJ
    c1
    @1
    elfzle2
    adantl
    #
    @4
    @1
    c1
    @4
    @1
    @13
    zcnd
    @4
    1cnd
    pncand
    breqtrrd
    lesubd
    @4
    @6
    @23
    @21
    cJ
    cif
    #
    @21
    @0
    @3
    @15
    @6
    @25
    wceq
    @19
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
    @4
    @23
    @21
    cJ
    @24
    iftrued
    eqtrd
    #
    breqtrrd
    @4
    @6
    @21
    @1
    cle
    @26
    @0
    @3
    @15
    @21
    @1
    cle
    wbr
    @19
    @0
    @15
    wa
    @1
    cJ
    @0
    @5
    @15
    @12
    adantr
    @15
    cJ
    cn
    wcel
    @0
    cJ
    @8
    elfznn
    adantl
    ltesubnnd
    syldan
    eqbrtrd
    @6
    c1
    @1
    elfz4
    syl32anc
end
