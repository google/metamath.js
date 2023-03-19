include "cdif.mm"
include "wcel.mm"
include "c1.mm"
include "wn.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "0re.mm"
include "1re.mm"
include "resubcli.mm"
include "clt.mm"
include "wbr.mm"
include "0lt1.mm"
include "cr.mm"
include "wb.mm"
include "ltsub23.mm"
include "mp3an.mm"
include "0m0e0.mm"
include "breq1i.mm"
include "bitr2i.mm"
include "mpbi.mm"
include "gtneii.mm"
include "nesymi.mm"
include "wi.mm"
include "caddc.mm"
include "eldifi.mm"
include "cn.mm"
include "1nn.mm"
include "a1i.mm"
include "ballotlemfp1.mm"
include "simpld.mm"
include "imp.mm"
include "1m1e0.mm"
include "fveq2i.mm"
include "oveq1i.mm"
include "ballotlemfval0.mm"
include "syl.mm"
include "adantr.mm"
include "oveq1d.mm"
include "3eqtrrd.mm"
include "eqeq1d.mm"
include "mtbii.mm"
include "cfz.mm"
include "ballotlemiex.mm"
include "simprd.mm"
include "ad2antrr.mm"
include "fveq2.mm"
include "adantl.mm"
include "mpbid.mm"
include "mtand.mm"
include "neqned.mm"

theorem ballotlemi1
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
  let vy: setvar y
  let vz: setvar z
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

  disjoint c k
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
  disjoint c y
  disjoint c z
  disjoint k y
  disjoint k z
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint F y
  disjoint F z
  disjoint M y
  disjoint M z
  disjoint N y
  disjoint N z
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint F j
  disjoint c d
  disjoint d k
  assert |- ( ( C e. ( O \ E ) /\ -. 1 e. C ) -> ( I ` C ) =/= 1 )

  proof
    cC
    cO
    cE
    cdif
    wcel
    #
    c1
    cC
    wcel
    #
    wn
    #
    wa
    #
    cC
    cI
    cfv
    #
    c1
    @3
    @4
    c1
    wceq
    #
    c1
    cC
    cF
    cfv
    #
    cfv
    #
    cc0
    wceq
    #
    @3
    cc0
    c1
    cmin
    co
    #
    cc0
    wceq
    @8
    cc0
    @9
    @9
    cc0
    cc0
    c1
    0re
    1re
    resubcli
    cc0
    c1
    clt
    wbr
    #
    @9
    cc0
    clt
    wbr
    #
    0lt1
    @11
    cc0
    cc0
    cmin
    co
    #
    c1
    clt
    wbr
    #
    @10
    cc0
    cr
    wcel
    #
    c1
    cr
    wcel
    @14
    @11
    @13
    wb
    0re
    1re
    0re
    cc0
    c1
    cc0
    ltsub23
    mp3an
    @12
    cc0
    c1
    clt
    0m0e0
    breq1i
    bitr2i
    mpbi
    gtneii
    nesymi
    @3
    @9
    @7
    cc0
    @3
    @7
    c1
    c1
    cmin
    co
    #
    @6
    cfv
    #
    c1
    cmin
    co
    #
    cc0
    @6
    cfv
    #
    c1
    cmin
    co
    #
    @9
    @0
    @2
    @7
    @17
    wceq
    #
    @0
    @2
    @20
    wi
    @1
    @7
    @16
    c1
    caddc
    co
    wceq
    wi
    @0
    vx
    cC
    cP
    vi
    cF
    c1
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    cC
    cO
    cE
    eldifi
    #
    c1
    cn
    wcel
    @0
    1nn
    a1i
    ballotlemfp1
    simpld
    imp
    @17
    @19
    wceq
    @3
    @16
    @18
    c1
    cmin
    @15
    cc0
    @6
    1m1e0
    fveq2i
    oveq1i
    a1i
    @3
    @18
    cc0
    c1
    cmin
    @0
    @18
    cc0
    wceq
    #
    @2
    @0
    cC
    cO
    wcel
    @22
    @21
    vx
    cC
    cP
    vi
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
    ballotlemfval0
    syl
    adantr
    oveq1d
    3eqtrrd
    eqeq1d
    mtbii
    @3
    @5
    wa
    @4
    @6
    cfv
    #
    cc0
    wceq
    #
    @8
    @0
    @24
    @2
    @5
    @0
    @4
    c1
    cM
    cN
    caddc
    co
    cfz
    co
    wcel
    @24
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
    simprd
    ad2antrr
    @5
    @24
    @8
    wb
    @3
    @5
    @23
    @7
    cc0
    @4
    c1
    @6
    fveq2
    eqeq1d
    adantl
    mpbid
    mtand
    neqned
end
