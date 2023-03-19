include "cdif.mm"
include "wcel.mm"
include "c1.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cmin.mm"
include "caddc.mm"
include "cc0.mm"
include "wceq.mm"
include "cneg.mm"
include "ballotlemsel1i.mm"
include "cz.mm"
include "wb.mm"
include "1zzd.mm"
include "ballotlemiex.mm"
include "adantr.mm"
include "simpld.mm"
include "elfzelz.mm"
include "syl.mm"
include "cuz.mm"
include "wss.mm"
include "elfzuz3.mm"
include "fzss2.mm"
include "3syl.mm"
include "simpr.mm"
include "sseldd.mm"
include "ballotlemsdom.mm"
include "syldan.mm"
include "fzsubel.mm"
include "syl22anc.mm"
include "mpbid.mm"
include "1m1e0.mm"
include "oveq1i.mm"
include "syl6eleq.mm"
include "cle.mm"
include "wbr.mm"
include "zsubcld.mm"
include "cn.mm"
include "nnaddcl.mm"
include "mp2an.mm"
include "nnzi.mm"
include "a1i.mm"
include "elfzle2.mm"
include "clt.mm"
include "zlem1lt.mm"
include "syl2anc.mm"
include "cr.mm"
include "wi.mm"
include "zred.mm"
include "ltle.mm"
include "sylbid.mm"
include "mpd.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "sselda.mm"
include "ballotlemfg.mm"
include "ballotlemfrc.mm"
include "oveq12d.mm"
include "cun.mm"
include "fzsplit3.mm"
include "oveq2d.mm"
include "1eluzge0.mm"
include "fzss1.mm"
include "ax-mp.mm"
include "sseli.mm"
include "sylan2.mm"
include "simprd.mm"
include "eqtr3d.mm"
include "cfn.mm"
include "fzfi.mm"
include "eldifi.mm"
include "chash.mm"
include "ballotlemelo.mm"
include "simplbi.mm"
include "ssfi.mm"
include "sylancr.mm"
include "fzfid.mm"
include "cin.mm"
include "c0.mm"
include "ltm1.mm"
include "fzdisj.mm"
include "ballotlemgun.mm"
include "3eqtr3rd.mm"
include "eqtrd.mm"
include "cc.mm"
include "ballotlemfelz.mm"
include "zcnd.mm"
include "ballotlemro.mm"
include "addeq0.mm"

theorem ballotlemfrceq
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let vi: setvar i
  let vk: setvar k
  let cE: class E
  let c.ex: class .^
  let cF: class F
  let cI: class I
  let cJ: class J
  let cM: class M
  let cN: class N
  let cO: class O
  let vc: setvar c
  let cU: class U
  let cV: class V
  let vj: setvar j
  let vd: setvar d
  let cD: class D
  assume ballotth.m: |- M e. NN
  assume ballotth.n: |- N e. NN
  assume ballotth.o: |- O = { c e. ~P ( 1 ... ( M + N ) ) | ( # ` c ) = M }
  assume ballotth.p: |- P = ( x e. ~P O |-> ( ( # ` x ) / ( # ` O ) ) )
  assume ballotth.f: |- F = ( c e. O |-> ( i e. ZZ |-> ( ( # ` ( ( 1 ... i ) i^i c ) ) - ( # ` ( ( 1 ... i ) \ c ) ) ) ) )
  assume ballotth.e: |- E = { c e. O | A. i e. ( 1 ... ( M + N ) ) 0 < ( ( F ` c ) ` i ) }
  assume ballotth.mgtn: |- N < M
  assume ballotth.i: |- I = ( c e. ( O \ E ) |-> inf ( { k e. ( 1 ... ( M + N ) ) | ( ( F ` c ) ` k ) = 0 } , RR , < ) )
  assume ballotth.s: |- S = ( c e. ( O \ E ) |-> ( i e. ( 1 ... ( M + N ) ) |-> if ( i <_ ( I ` c ) , ( ( ( I ` c ) + 1 ) - i ) , i ) ) )
  assume ballotth.r: |- R = ( c e. ( O \ E ) |-> ( ( S ` c ) " c ) )
  assume ballotlemg: |- .^ = ( u e. Fin , v e. Fin |-> ( ( # ` ( v i^i u ) ) - ( # ` ( v \ u ) ) ) )

  disjoint u v
  disjoint C u
  disjoint C v
  disjoint I u
  disjoint I v
  disjoint J u
  disjoint J v
  disjoint R u
  disjoint R v
  disjoint S u
  disjoint S v
  disjoint J i
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
  disjoint S i
  disjoint S c
  disjoint R i
  disjoint U u
  disjoint U v
  disjoint V u
  disjoint V v
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
  disjoint D i
  disjoint D k
  assert |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( I ` C ) ) ) -> ( ( F ` C ) ` ( ( ( S ` C ) ` J ) - 1 ) ) = -u ( ( F ` ( R ` C ) ) ` J ) )

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
    cJ
    cC
    cS
    cfv
    cfv
    #
    c1
    cmin
    co
    #
    cC
    cF
    cfv
    #
    cfv
    #
    cJ
    cC
    cR
    cfv
    #
    cF
    cfv
    cfv
    #
    caddc
    co
    #
    cc0
    wceq
    #
    @8
    @10
    cneg
    wceq
    #
    @4
    @11
    cC
    c1
    @6
    cfz
    co
    #
    c.ex
    co
    #
    cC
    @5
    @1
    cfz
    co
    #
    c.ex
    co
    #
    caddc
    co
    #
    cc0
    @4
    @8
    @15
    @10
    @17
    caddc
    @0
    @3
    @6
    cc0
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
    @8
    @15
    wceq
    @0
    @3
    @6
    cc0
    @1
    c1
    cmin
    co
    #
    cfz
    co
    #
    wcel
    @21
    @4
    @6
    c1
    c1
    cmin
    co
    #
    @22
    cfz
    co
    #
    @23
    @4
    @5
    @2
    wcel
    #
    @6
    @25
    wcel
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
    ballotlemsel1i
    #
    @4
    c1
    cz
    wcel
    #
    @1
    cz
    wcel
    #
    @5
    cz
    wcel
    #
    @29
    @26
    @27
    wb
    @4
    1zzd
    #
    @4
    @1
    c1
    @19
    cfz
    co
    #
    wcel
    #
    @30
    @4
    @34
    @1
    @7
    cfv
    #
    cc0
    wceq
    #
    @0
    @34
    @36
    wa
    @3
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
    adantr
    #
    simpld
    #
    @1
    c1
    @19
    elfzelz
    #
    syl
    @4
    @5
    @33
    wcel
    #
    @31
    @0
    @3
    cJ
    @33
    wcel
    @41
    @4
    @2
    @33
    cJ
    @4
    @34
    @19
    @1
    cuz
    cfv
    wcel
    @2
    @33
    wss
    @39
    @1
    c1
    @19
    elfzuz3
    @1
    c1
    @19
    fzss2
    3syl
    @0
    @3
    simpr
    #
    sseldd
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
    @5
    c1
    @19
    elfzelz
    syl
    #
    @32
    @5
    c1
    c1
    @1
    fzsubel
    syl22anc
    mpbid
    @24
    cc0
    @22
    cfz
    1m1e0
    oveq1i
    syl6eleq
    @0
    @23
    @20
    @6
    @0
    @19
    @22
    cuz
    cfv
    wcel
    #
    @23
    @20
    wss
    @0
    @22
    cz
    wcel
    @19
    cz
    wcel
    #
    @22
    @19
    cle
    wbr
    #
    @44
    @0
    @1
    c1
    @0
    @34
    @30
    @0
    @34
    @36
    @37
    simpld
    #
    @40
    syl
    #
    @0
    1zzd
    zsubcld
    #
    @45
    @0
    @19
    cM
    cn
    wcel
    cN
    cn
    wcel
    @19
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
    #
    @0
    @1
    @19
    cle
    wbr
    #
    @46
    @0
    @34
    @51
    @47
    @1
    c1
    @19
    elfzle2
    syl
    @0
    @51
    @22
    @19
    clt
    wbr
    #
    @46
    @0
    @30
    @45
    @51
    @52
    wb
    @48
    @50
    @1
    @19
    zlem1lt
    syl2anc
    @0
    @22
    cr
    wcel
    @19
    cr
    wcel
    @52
    @46
    wi
    @0
    @22
    @49
    zred
    @0
    @19
    @50
    zred
    @22
    @19
    ltle
    syl2anc
    sylbid
    mpd
    @22
    @19
    eluz2
    syl3anbrc
    @22
    cc0
    @19
    fzss2
    syl
    sselda
    syldan
    vx
    vv
    vu
    cC
    cP
    cR
    cS
    vi
    vk
    cE
    c.ex
    cF
    cI
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
    ballotth.e
    ballotth.mgtn
    ballotth.i
    ballotth.s
    ballotth.r
    ballotlemg
    ballotlemfg
    syldan
    vx
    vv
    vu
    cC
    cP
    cR
    cS
    vi
    vk
    cE
    c.ex
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
    ballotth.r
    ballotlemg
    ballotlemfrc
    oveq12d
    @4
    cC
    @2
    c.ex
    co
    #
    cC
    @14
    @16
    cun
    #
    c.ex
    co
    cc0
    @18
    @4
    @2
    @54
    cC
    c.ex
    @4
    @26
    @2
    @54
    wceq
    @28
    @5
    c1
    @1
    fzsplit3
    syl
    oveq2d
    @4
    @35
    @53
    cc0
    @0
    @3
    @34
    @35
    @53
    wceq
    #
    @39
    @34
    @0
    @1
    @20
    wcel
    @55
    @33
    @20
    @1
    c1
    cc0
    cuz
    cfv
    wcel
    @33
    @20
    wss
    1eluzge0
    c1
    cc0
    @19
    fzss1
    ax-mp
    sseli
    vx
    vv
    vu
    cC
    cP
    cR
    cS
    vi
    vk
    cE
    c.ex
    cF
    cI
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
    ballotth.e
    ballotth.mgtn
    ballotth.i
    ballotth.s
    ballotth.r
    ballotlemg
    ballotlemfg
    sylan2
    syldan
    @4
    @34
    @36
    @38
    simprd
    eqtr3d
    @4
    vx
    vv
    vu
    cP
    cR
    cS
    cC
    vi
    vk
    cE
    c.ex
    cF
    cI
    cM
    cN
    cO
    @14
    @16
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
    ballotth.r
    ballotlemg
    @0
    cC
    cfn
    wcel
    #
    @3
    @0
    @33
    cfn
    wcel
    cC
    @33
    wss
    #
    @56
    c1
    @19
    fzfi
    @0
    cC
    cO
    wcel
    #
    @57
    cC
    cO
    cE
    eldifi
    #
    @58
    @57
    cC
    chash
    cfv
    cM
    wceq
    cC
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotlemelo
    simplbi
    syl
    @33
    cC
    ssfi
    sylancr
    adantr
    @4
    c1
    @6
    fzfid
    @4
    @5
    @1
    fzfid
    @4
    @5
    cr
    wcel
    @6
    @5
    clt
    wbr
    @14
    @16
    cin
    c0
    wceq
    @4
    @5
    @43
    zred
    @5
    ltm1
    c1
    @6
    @5
    @1
    fzdisj
    3syl
    ballotlemgun
    3eqtr3rd
    eqtrd
    @4
    @8
    cc
    wcel
    @10
    cc
    wcel
    @12
    @13
    wb
    @4
    @8
    @4
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
    @58
    @3
    @59
    adantr
    @4
    @5
    c1
    @43
    @32
    zsubcld
    ballotlemfelz
    zcnd
    @4
    @10
    @4
    vx
    @9
    cP
    vi
    cF
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
    @0
    @9
    cO
    wcel
    @3
    vx
    cC
    cP
    cR
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
    ballotth.r
    ballotlemro
    adantr
    @4
    @3
    cJ
    cz
    wcel
    @42
    cJ
    c1
    @1
    elfzelz
    syl
    ballotlemfelz
    zcnd
    @8
    @10
    addeq0
    syl2anc
    mpbid
end
