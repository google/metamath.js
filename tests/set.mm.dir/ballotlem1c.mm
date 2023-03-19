include "cdif.mm"
include "wcel.mm"
include "c1.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "wrex.mm"
include "eldifi.mm"
include "ad2antrr.mm"
include "cn.mm"
include "c2.mm"
include "cuz.mm"
include "wne.mm"
include "caddc.mm"
include "ballotlemiex.mm"
include "simpld.mm"
include "elfznn.mm"
include "syl.mm"
include "adantr.mm"
include "ballotlemii.mm"
include "eluz2b3.mm"
include "sylanbrc.mm"
include "uz2m1nn.mm"
include "cle.mm"
include "wbr.mm"
include "elnnuz.mm"
include "biimpi.mm"
include "eluzfz1.mm"
include "3syl.mm"
include "0le1.mm"
include "1e0p1.mm"
include "breqtri.mm"
include "wn.mm"
include "wi.mm"
include "1nn.mm"
include "a1i.mm"
include "ballotlemfp1.mm"
include "simprd.mm"
include "imp.mm"
include "1m1e0.mm"
include "fveq2i.mm"
include "oveq1i.mm"
include "ballotlemfval0.mm"
include "oveq1d.mm"
include "3eqtrrd.mm"
include "syl5breq.mm"
include "fveq2.mm"
include "breq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "clt.mm"
include "cneg.mm"
include "df-neg.mm"
include "eqtr3d.mm"
include "0cnd.mm"
include "1cnd.mm"
include "cz.mm"
include "nnzd.mm"
include "1zzd.mm"
include "zsubcld.mm"
include "ballotlemfelz.mm"
include "zcnd.mm"
include "subadd2d.mm"
include "mpbird.mm"
include "syl5eq.mm"
include "neg1lt0.mm"
include "syl6eqbrr.mm"
include "adantlr.mm"
include "ballotlemfcc.mm"
include "ballotlemimin.mm"
include "pm2.65da.mm"

theorem ballotlem1c
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
  let vw: setvar w
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
  disjoint k w
  disjoint w y
  disjoint w z
  disjoint C w
  disjoint F w
  disjoint M w
  disjoint N w
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint F j
  disjoint c d
  disjoint d k
  assert |- ( ( C e. ( O \ E ) /\ 1 e. C ) -> -. ( I ` C ) e. C )

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
    wa
    #
    cC
    cI
    cfv
    #
    cC
    wcel
    #
    vk
    cv
    cC
    cF
    cfv
    #
    cfv
    cc0
    wceq
    vk
    c1
    @3
    c1
    cmin
    co
    #
    cfz
    co
    #
    wrex
    #
    @2
    @4
    wa
    #
    vx
    cC
    cP
    vi
    vk
    cF
    @6
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
    cC
    cO
    wcel
    #
    @1
    @4
    cC
    cO
    cE
    eldifi
    #
    ad2antrr
    @2
    @6
    cn
    wcel
    #
    @4
    @2
    @3
    c2
    cuz
    cfv
    wcel
    #
    @12
    @2
    @3
    cn
    wcel
    #
    @3
    c1
    wne
    @13
    @0
    @14
    @1
    @0
    @3
    c1
    cM
    cN
    caddc
    co
    #
    cfz
    co
    wcel
    #
    @14
    @0
    @16
    @3
    @5
    cfv
    #
    cc0
    wceq
    #
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
    #
    simpld
    @3
    @15
    elfznn
    syl
    #
    adantr
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
    ballotlemii
    @3
    eluz2b3
    sylanbrc
    @3
    uz2m1nn
    syl
    #
    adantr
    @9
    c1
    @7
    wcel
    #
    cc0
    c1
    @5
    cfv
    #
    cle
    wbr
    #
    cc0
    vi
    cv
    #
    @5
    cfv
    #
    cle
    wbr
    #
    vi
    @7
    wrex
    @2
    @22
    @4
    @2
    @12
    @6
    c1
    cuz
    cfv
    wcel
    #
    @22
    @21
    @12
    @28
    @6
    elnnuz
    biimpi
    c1
    @6
    eluzfz1
    3syl
    adantr
    @2
    @24
    @4
    @2
    cc0
    cc0
    c1
    caddc
    co
    #
    @23
    cle
    cc0
    c1
    @29
    cle
    0le1
    1e0p1
    breqtri
    @2
    @23
    c1
    c1
    cmin
    co
    #
    @5
    cfv
    #
    c1
    caddc
    co
    #
    cc0
    @5
    cfv
    #
    c1
    caddc
    co
    #
    @29
    @0
    @1
    @23
    @32
    wceq
    #
    @0
    @1
    wn
    @23
    @31
    c1
    cmin
    co
    wceq
    wi
    @1
    @35
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
    @11
    c1
    cn
    wcel
    @0
    1nn
    a1i
    ballotlemfp1
    simprd
    imp
    @32
    @34
    wceq
    @2
    @31
    @33
    c1
    caddc
    @30
    cc0
    @5
    1m1e0
    fveq2i
    oveq1i
    a1i
    @2
    @33
    cc0
    c1
    caddc
    @0
    @33
    cc0
    wceq
    #
    @1
    @0
    @10
    @36
    @11
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
    syl5breq
    adantr
    @27
    @24
    vi
    c1
    @7
    @25
    c1
    wceq
    @26
    @23
    cc0
    cle
    @25
    c1
    @5
    fveq2
    breq2d
    rspcev
    syl2anc
    @0
    @4
    @6
    @5
    cfv
    #
    cc0
    clt
    wbr
    @1
    @0
    @4
    wa
    #
    @37
    c1
    cneg
    #
    cc0
    clt
    @38
    @39
    cc0
    c1
    cmin
    co
    #
    @37
    c1
    df-neg
    @38
    @40
    @37
    wceq
    @37
    c1
    caddc
    co
    #
    cc0
    wceq
    @38
    @17
    @41
    cc0
    @0
    @4
    @17
    @41
    wceq
    #
    @0
    @4
    wn
    @17
    @37
    c1
    cmin
    co
    wceq
    wi
    @4
    @42
    wi
    @0
    vx
    cC
    cP
    vi
    cF
    @3
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    @11
    @20
    ballotlemfp1
    simprd
    imp
    @0
    @18
    @4
    @0
    @16
    @18
    @19
    simprd
    adantr
    eqtr3d
    @38
    cc0
    c1
    @37
    @38
    0cnd
    @38
    1cnd
    @38
    @37
    @38
    vx
    cC
    cP
    vi
    cF
    @6
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
    @10
    @4
    @11
    adantr
    @38
    @3
    c1
    @0
    @3
    cz
    wcel
    @4
    @0
    @3
    @20
    nnzd
    adantr
    @38
    1zzd
    zsubcld
    ballotlemfelz
    zcnd
    subadd2d
    mpbird
    syl5eq
    neg1lt0
    syl6eqbrr
    adantlr
    ballotlemfcc
    @0
    @8
    wn
    @1
    @4
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
    ballotlemimin
    ad2antrr
    pm2.65da
end
