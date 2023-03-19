include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cfv.mm"
include "c1.mm"
include "cfz.mm"
include "cin.mm"
include "chash.mm"
include "cdif.mm"
include "cmin.mm"
include "id.mm"
include "cz.mm"
include "cn.mm"
include "nnaddcl.mm"
include "mp2an.mm"
include "nnzi.mm"
include "a1i.mm"
include "ballotlemfval.mm"
include "wss.mm"
include "wceq.mm"
include "cpw.mm"
include "cv.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseli.mm"
include "elpwid.mm"
include "sseqin2.mm"
include "sylib.mm"
include "fveq2d.mm"
include "cab.mm"
include "rabssab.mm"
include "eleq2s.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "cbvabv.mm"
include "elab2g.mm"
include "mpbid.mm"
include "eqtrd.mm"
include "cfn.mm"
include "fzfi.mm"
include "hashssdif.mm"
include "sylancr.mm"
include "cn0.mm"
include "nnnn0i.mm"
include "hashfz1.mm"
include "mp1i.mm"
include "oveq12d.mm"
include "cc.mm"
include "nncni.mm"
include "pncan2.mm"
include "3eqtrd.mm"

theorem ballotlemfmpn
  let vx: setvar x
  let cC: class C
  let cP: class P
  let vi: setvar i
  let cF: class F
  let cM: class M
  let cN: class N
  let cO: class O
  let vc: setvar c
  let vb: setvar b
  let vj: setvar j
  let vk: setvar k
  assume ballotth.m: |- M e. NN
  assume ballotth.n: |- N e. NN
  assume ballotth.o: |- O = { c e. ~P ( 1 ... ( M + N ) ) | ( # ` c ) = M }
  assume ballotth.p: |- P = ( x e. ~P O |-> ( ( # ` x ) / ( # ` O ) ) )
  assume ballotth.f: |- F = ( c e. O |-> ( i e. ZZ |-> ( ( # ` ( ( 1 ... i ) i^i c ) ) - ( # ` ( ( 1 ... i ) \ c ) ) ) ) )

  disjoint M c
  disjoint M c
  disjoint N c
  disjoint O c
  disjoint M i
  disjoint N i
  disjoint O i
  disjoint c i
  disjoint F c
  disjoint F i
  disjoint C i
  disjoint b c
  disjoint M b
  disjoint C b
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint M k
  disjoint N k
  disjoint O k
  disjoint F j
  disjoint F k
  assert |- ( C e. O -> ( ( F ` C ) ` ( M + N ) ) = ( M - N ) )

  proof
    cC
    cO
    wcel
    #
    cM
    cN
    caddc
    co
    #
    cC
    cF
    cfv
    cfv
    c1
    @1
    cfz
    co
    #
    cC
    cin
    #
    chash
    cfv
    #
    @2
    cC
    cdif
    chash
    cfv
    #
    cmin
    co
    cM
    cN
    cmin
    co
    @0
    vx
    cC
    cP
    vi
    cF
    @1
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    @0
    id
    @1
    cz
    wcel
    @0
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
    #
    nnzi
    a1i
    ballotlemfval
    @0
    @4
    cM
    @5
    cN
    cmin
    @0
    @4
    cC
    chash
    cfv
    #
    cM
    @0
    @3
    cC
    chash
    @0
    cC
    @2
    wss
    #
    @3
    cC
    wceq
    @0
    cC
    @2
    cO
    @2
    cpw
    #
    cC
    cO
    vc
    cv
    #
    chash
    cfv
    #
    cM
    wceq
    #
    vc
    @9
    crab
    #
    @9
    ballotth.o
    @12
    vc
    @9
    ssrab2
    eqsstri
    sseli
    elpwid
    #
    cC
    @2
    sseqin2
    sylib
    fveq2d
    @0
    cC
    @12
    vc
    cab
    #
    wcel
    #
    @7
    cM
    wceq
    #
    @16
    cC
    @13
    cO
    @13
    @15
    cC
    @12
    vc
    @9
    rabssab
    sseli
    ballotth.o
    eleq2s
    vb
    cv
    #
    chash
    cfv
    #
    cM
    wceq
    #
    @17
    vb
    cC
    @15
    cO
    @18
    cC
    wceq
    @19
    @7
    cM
    @18
    cC
    chash
    fveq2
    eqeq1d
    @12
    @20
    vc
    vb
    @10
    @18
    wceq
    @11
    @19
    cM
    @10
    @18
    chash
    fveq2
    eqeq1d
    cbvabv
    elab2g
    mpbid
    #
    eqtrd
    @0
    @5
    @2
    chash
    cfv
    #
    @7
    cmin
    co
    #
    @1
    cM
    cmin
    co
    #
    cN
    @0
    @2
    cfn
    wcel
    @8
    @5
    @23
    wceq
    c1
    @1
    fzfi
    @14
    @2
    cC
    hashssdif
    sylancr
    @0
    @22
    @1
    @7
    cM
    cmin
    @1
    cn0
    wcel
    @22
    @1
    wceq
    @0
    @1
    @6
    nnnn0i
    @1
    hashfz1
    mp1i
    @21
    oveq12d
    @24
    cN
    wceq
    #
    @0
    cM
    cc
    wcel
    cN
    cc
    wcel
    @25
    cM
    ballotth.m
    nncni
    cN
    ballotth.n
    nncni
    cM
    cN
    pncan2
    mp2an
    a1i
    3eqtrd
    oveq12d
    eqtrd
end
