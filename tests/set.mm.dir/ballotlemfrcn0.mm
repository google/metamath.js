include "cdif.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cc0.mm"
include "wne.mm"
include "cmin.mm"
include "wceq.mm"
include "wn.mm"
include "cz.mm"
include "cle.mm"
include "1zzd.mm"
include "cn.mm"
include "nnaddcl.mm"
include "mp2an.mm"
include "nnzi.mm"
include "a1i.mm"
include "wa.mm"
include "ballotlemsdom.mm"
include "elfzelz.mm"
include "syl.mm"
include "3adant3.mm"
include "zsubcld.mm"
include "ballotlemsgt1.mm"
include "zltlem1.mm"
include "biimpa.mm"
include "syl21anc.mm"
include "zred.mm"
include "1red.mm"
include "resubcld.mm"
include "simp1.mm"
include "ballotlemiex.mm"
include "simpld.mm"
include "3syl.mm"
include "3ad2ant2.mm"
include "elfzle1.mm"
include "simp3.mm"
include "ltled.mm"
include "elfz4.mm"
include "syl32anc.mm"
include "ballotlemsel1i.mm"
include "syl2anc.mm"
include "elfzle2.mm"
include "wb.mm"
include "zlem1lt.mm"
include "mpbid.mm"
include "letrd.mm"
include "wi.mm"
include "cv.mm"
include "crab.mm"
include "cr.mm"
include "cinf.mm"
include "biid.mm"
include "sylibr.mm"
include "ballotlemi.mm"
include "breq2d.mm"
include "3ad2ant1.mm"
include "wor.mm"
include "ltso.mm"
include "ballotlemsup.mm"
include "inflb.mm"
include "con2d.mm"
include "sylc.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "sylnib.mm"
include "imnan.mm"
include "mpd.mm"
include "neqned.mm"
include "cneg.mm"
include "ballotlemro.mm"
include "adantr.mm"
include "adantl.mm"
include "ballotlemfelz.mm"
include "zcnd.mm"
include "negeq0d.mm"
include "cfn.mm"
include "cin.mm"
include "chash.mm"
include "cmpt2.mm"
include "eqid.mm"
include "ballotlemfrceq.mm"
include "bitr4d.mm"
include "necon3bid.mm"
include "mpbird.mm"

theorem ballotlemfrcn0
  let vx: setvar x
  let cC: class C
  let cP: class P
  let cR: class R
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
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
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

  disjoint c k
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
  disjoint w y
  disjoint w z
  disjoint y z
  disjoint c y
  disjoint c z
  disjoint k y
  disjoint k z
  disjoint C y
  disjoint C z
  disjoint F y
  disjoint F z
  disjoint M y
  disjoint M z
  disjoint N y
  disjoint N z
  disjoint k w
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
  disjoint i j
  disjoint I j
  disjoint C j
  disjoint E j
  disjoint J j
  disjoint j k
  disjoint S j
  disjoint D i
  disjoint D k
  assert |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( M + N ) ) /\ J < ( I ` C ) ) -> ( ( F ` ( R ` C ) ) ` J ) =/= 0 )

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
    cJ
    cC
    cI
    cfv
    #
    clt
    wbr
    #
    w3a
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
    cc0
    wne
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
    cc0
    wne
    #
    @6
    @13
    cc0
    @6
    @11
    @2
    wcel
    #
    @13
    cc0
    wceq
    #
    wn
    #
    @6
    c1
    cz
    wcel
    #
    @1
    cz
    wcel
    #
    @11
    cz
    wcel
    c1
    @11
    cle
    wbr
    #
    @11
    @1
    cle
    wbr
    @15
    @6
    1zzd
    #
    @19
    @6
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
    #
    @6
    @10
    c1
    @0
    @3
    @10
    cz
    wcel
    #
    @5
    @0
    @3
    wa
    @10
    @2
    wcel
    @23
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
    @10
    c1
    @1
    elfzelz
    syl
    3adant3
    #
    @21
    zsubcld
    @6
    @18
    @23
    c1
    @10
    clt
    wbr
    #
    @20
    @21
    @24
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
    ballotlemsgt1
    @18
    @23
    wa
    @25
    @20
    c1
    @10
    zltlem1
    biimpa
    syl21anc
    @6
    @11
    @4
    @1
    @6
    @10
    c1
    @6
    @10
    @24
    zred
    @6
    1red
    resubcld
    #
    @6
    @4
    @6
    @0
    @4
    @2
    wcel
    #
    @4
    cz
    wcel
    #
    @0
    @3
    @5
    simp1
    #
    @0
    @27
    @4
    @12
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
    @4
    c1
    @1
    elfzelz
    3syl
    #
    zred
    #
    @6
    @1
    @22
    zred
    @6
    @11
    @4
    @26
    @32
    @6
    @10
    @4
    cle
    wbr
    #
    @11
    @4
    clt
    wbr
    #
    @6
    @10
    c1
    @4
    cfz
    co
    #
    wcel
    #
    @33
    @6
    @0
    cJ
    @35
    wcel
    #
    @36
    @29
    @6
    @18
    @28
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
    @4
    cle
    wbr
    @37
    @21
    @31
    @3
    @0
    @38
    @5
    cJ
    c1
    @1
    elfzelz
    3ad2ant2
    #
    @3
    @0
    @39
    @5
    cJ
    c1
    @1
    elfzle1
    3ad2ant2
    @6
    cJ
    @4
    @6
    cJ
    @40
    zred
    @32
    @0
    @3
    @5
    simp3
    ltled
    cJ
    c1
    @4
    elfz4
    syl32anc
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
    syl2anc
    @10
    c1
    @4
    elfzle2
    syl
    @6
    @23
    @28
    @33
    @34
    wb
    @24
    @31
    @10
    @4
    zlem1lt
    syl2anc
    mpbid
    #
    ltled
    @6
    @0
    @27
    @4
    @1
    cle
    wbr
    @29
    @30
    @4
    c1
    @1
    elfzle2
    3syl
    letrd
    @11
    c1
    @1
    elfz4
    syl32anc
    @6
    @15
    @16
    wa
    #
    wn
    @15
    @17
    wi
    @6
    @11
    vk
    cv
    #
    @12
    cfv
    #
    cc0
    wceq
    #
    vk
    @2
    crab
    #
    wcel
    #
    @43
    @6
    @0
    @11
    @47
    cr
    clt
    cinf
    #
    clt
    wbr
    #
    @48
    wn
    @29
    @6
    @34
    @50
    @6
    @34
    @34
    @42
    @34
    biid
    sylibr
    @0
    @3
    @34
    @50
    wb
    @5
    @0
    @4
    @49
    @11
    clt
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
    breq2d
    3ad2ant1
    mpbid
    @0
    @48
    @50
    @0
    vz
    vw
    vy
    cr
    @47
    @11
    clt
    cr
    clt
    wor
    @0
    ltso
    a1i
    vx
    vy
    vz
    vw
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
    ballotlemsup
    inflb
    con2d
    sylc
    @46
    @16
    vk
    @11
    @2
    @44
    @11
    wceq
    @45
    @13
    cc0
    @44
    @11
    @12
    fveq2
    eqeq1d
    elrab
    sylnib
    @15
    @16
    imnan
    sylibr
    mpd
    neqned
    @6
    @0
    @37
    @9
    @14
    wb
    @29
    @41
    @0
    @37
    wa
    #
    @8
    cc0
    @13
    cc0
    @51
    @8
    cc0
    wceq
    @8
    cneg
    #
    cc0
    wceq
    @16
    @51
    @8
    @51
    @8
    @51
    vx
    @7
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
    @7
    cO
    wcel
    @37
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
    @37
    @38
    @0
    cJ
    c1
    @4
    elfzelz
    adantl
    ballotlemfelz
    zcnd
    negeq0d
    @51
    @13
    @52
    cc0
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
    vu
    vv
    cfn
    cfn
    vv
    cv
    #
    vu
    cv
    #
    cin
    chash
    cfv
    @53
    @54
    cdif
    chash
    cfv
    cmin
    co
    cmpt2
    #
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
    @55
    eqid
    ballotlemfrceq
    eqeq1d
    bitr4d
    necon3bid
    syl2anc
    mpbird
end
