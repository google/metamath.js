include "cdif.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "crab.mm"
include "wa.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "ballotlemi.mm"
include "wor.mm"
include "cfn.mm"
include "c0.mm"
include "wne.mm"
include "wss.mm"
include "ltso.mm"
include "a1i.mm"
include "fzfi.mm"
include "ssrab2.mm"
include "ssfi.mm"
include "mp2an.mm"
include "wrex.mm"
include "ballotlem5.mm"
include "rabn0.mm"
include "sylibr.mm"
include "cz.mm"
include "cuz.mm"
include "fzssuz.mm"
include "uzssz.mm"
include "sstri.mm"
include "zssre.mm"
include "fiinfcl.mm"
include "syl13anc.mm"
include "eqeltrd.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "sylib.mm"

theorem ballotlemiex
  let vx: setvar x
  let cC: class C
  let cP: class P
  let vi: setvar i
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cI: class I
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
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint F j
  disjoint c d
  disjoint d k
  assert |- ( C e. ( O \ E ) -> ( ( I ` C ) e. ( 1 ... ( M + N ) ) /\ ( ( F ` C ) ` ( I ` C ) ) = 0 ) )

  proof
    cC
    cO
    cE
    cdif
    wcel
    #
    cC
    cI
    cfv
    #
    vk
    cv
    #
    cC
    cF
    cfv
    #
    cfv
    #
    cc0
    wceq
    #
    vk
    c1
    cM
    cN
    caddc
    co
    #
    cfz
    co
    #
    crab
    #
    wcel
    @1
    @7
    wcel
    @1
    @3
    cfv
    #
    cc0
    wceq
    #
    wa
    @0
    @1
    @8
    cr
    clt
    cinf
    #
    @8
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
    ballotlemi
    @0
    cr
    clt
    wor
    #
    @8
    cfn
    wcel
    #
    @8
    c0
    wne
    #
    @8
    cr
    wss
    #
    @11
    @8
    wcel
    @12
    @0
    ltso
    a1i
    @13
    @0
    @7
    cfn
    wcel
    @8
    @7
    wss
    @13
    c1
    @6
    fzfi
    @5
    vk
    @7
    ssrab2
    #
    @7
    @8
    ssfi
    mp2an
    a1i
    @0
    @5
    vk
    @7
    wrex
    @14
    vx
    cC
    cP
    vi
    vk
    cE
    cF
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
    ballotlem5
    @5
    vk
    @7
    rabn0
    sylibr
    @15
    @0
    @8
    @7
    cr
    @16
    @7
    cz
    cr
    @7
    c1
    cuz
    cfv
    cz
    c1
    @6
    fzssuz
    c1
    uzssz
    sstri
    zssre
    sstri
    sstri
    a1i
    cr
    @8
    clt
    fiinfcl
    syl13anc
    eqeltrd
    @5
    @10
    vk
    @1
    @7
    @2
    @1
    wceq
    @4
    @9
    cc0
    @2
    @1
    @3
    fveq2
    eqeq1d
    elrab
    sylib
end
