include "cdif.mm"
include "wcel.mm"
include "c1.mm"
include "wn.mm"
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
include "ballotlemi1.mm"
include "eluz2b3.mm"
include "sylanbrc.mm"
include "uz2m1nn.mm"
include "cle.mm"
include "wbr.mm"
include "elnnuz.mm"
include "biimpi.mm"
include "eluzfz1.mm"
include "3syl.mm"
include "wi.mm"
include "1nn.mm"
include "a1i.mm"
include "ballotlemfp1.mm"
include "imp.mm"
include "1m1e0.mm"
include "fveq2i.mm"
include "oveq1i.mm"
include "ballotlemfval0.mm"
include "oveq1d.mm"
include "3eqtrrd.mm"
include "0le1.mm"
include "cr.mm"
include "wb.mm"
include "0re.mm"
include "1re.mm"
include "suble0.mm"
include "mp2an.mm"
include "mpbir.mm"
include "syl6eqbrr.mm"
include "fveq2.mm"
include "breq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "clt.mm"
include "0lt1.mm"
include "1p0e1.mm"
include "simprd.mm"
include "eqtr3d.mm"
include "cz.mm"
include "nnzd.mm"
include "1zzd.mm"
include "zsubcld.mm"
include "ballotlemfelz.mm"
include "zcnd.mm"
include "1cnd.mm"
include "0cnd.mm"
include "subaddd.mm"
include "mpbid.mm"
include "syl5eqr.mm"
include "syl5breq.mm"
include "adantlr.mm"
include "ballotlemfc0.mm"
include "ballotlemimin.mm"
include "condan.mm"

theorem ballotlemic
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
  assert |- ( ( C e. ( O \ E ) /\ -. 1 e. C ) -> ( I ` C ) e. C )

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
    @4
    c1
    cmin
    co
    #
    cfz
    co
    #
    wrex
    #
    @3
    @5
    wn
    #
    wa
    #
    vx
    cC
    cP
    vi
    vk
    cF
    @7
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
    @2
    @10
    cC
    cO
    cE
    eldifi
    #
    ad2antrr
    @3
    @7
    cn
    wcel
    #
    @10
    @3
    @4
    c2
    cuz
    cfv
    wcel
    #
    @14
    @3
    @4
    cn
    wcel
    #
    @4
    c1
    wne
    @15
    @0
    @16
    @2
    @0
    @4
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
    @16
    @0
    @18
    @4
    @6
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
    @4
    @17
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
    ballotlemi1
    @4
    eluz2b3
    sylanbrc
    @4
    uz2m1nn
    syl
    #
    adantr
    @11
    c1
    @8
    wcel
    #
    c1
    @6
    cfv
    #
    cc0
    cle
    wbr
    #
    vi
    cv
    #
    @6
    cfv
    #
    cc0
    cle
    wbr
    #
    vi
    @8
    wrex
    @3
    @24
    @10
    @3
    @14
    @7
    c1
    cuz
    cfv
    wcel
    #
    @24
    @23
    @14
    @30
    @7
    elnnuz
    biimpi
    c1
    @7
    eluzfz1
    3syl
    adantr
    @3
    @26
    @10
    @3
    @25
    cc0
    c1
    cmin
    co
    #
    cc0
    cle
    @3
    @25
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
    @31
    @0
    @2
    @25
    @34
    wceq
    #
    @0
    @2
    @37
    wi
    @1
    @25
    @33
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
    @13
    c1
    cn
    wcel
    @0
    1nn
    a1i
    ballotlemfp1
    simpld
    imp
    @34
    @36
    wceq
    @3
    @33
    @35
    c1
    cmin
    @32
    cc0
    @6
    1m1e0
    fveq2i
    oveq1i
    a1i
    @3
    @35
    cc0
    c1
    cmin
    @0
    @35
    cc0
    wceq
    #
    @2
    @0
    @12
    @38
    @13
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
    @31
    cc0
    cle
    wbr
    #
    cc0
    c1
    cle
    wbr
    #
    0le1
    cc0
    cr
    wcel
    c1
    cr
    wcel
    @39
    @40
    wb
    0re
    1re
    cc0
    c1
    suble0
    mp2an
    mpbir
    syl6eqbrr
    adantr
    @29
    @26
    vi
    c1
    @8
    @27
    c1
    wceq
    @28
    @25
    cc0
    cle
    @27
    c1
    @6
    fveq2
    breq1d
    rspcev
    syl2anc
    @0
    @10
    cc0
    @7
    @6
    cfv
    #
    clt
    wbr
    @2
    @0
    @10
    wa
    #
    cc0
    c1
    @41
    clt
    0lt1
    @42
    c1
    c1
    cc0
    caddc
    co
    #
    @41
    1p0e1
    @42
    @41
    c1
    cmin
    co
    #
    cc0
    wceq
    @43
    @41
    wceq
    @42
    @19
    @44
    cc0
    @0
    @10
    @19
    @44
    wceq
    #
    @0
    @10
    @45
    wi
    @5
    @19
    @41
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
    @4
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    @13
    @22
    ballotlemfp1
    simpld
    imp
    @0
    @20
    @10
    @0
    @18
    @20
    @21
    simprd
    adantr
    eqtr3d
    @42
    @41
    c1
    cc0
    @42
    @41
    @42
    vx
    cC
    cP
    vi
    cF
    @7
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
    @12
    @10
    @13
    adantr
    @42
    @4
    c1
    @0
    @4
    cz
    wcel
    @10
    @0
    @4
    @22
    nnzd
    adantr
    @42
    1zzd
    zsubcld
    ballotlemfelz
    zcnd
    @42
    1cnd
    @42
    0cnd
    subaddd
    mpbid
    syl5eqr
    syl5breq
    adantlr
    ballotlemfc0
    @0
    @9
    wn
    @2
    @10
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
    condan
end
