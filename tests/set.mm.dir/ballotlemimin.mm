include "cdif.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "elfzle2.mm"
include "adantl.mm"
include "cz.mm"
include "wb.mm"
include "elfzelz.mm"
include "caddc.mm"
include "cn.mm"
include "ballotlemiex.mm"
include "simpld.mm"
include "elfznn.mm"
include "syl.mm"
include "nnzd.mm"
include "zltlem1.mm"
include "syl2anr.mm"
include "mpbird.mm"
include "adantr.mm"
include "wn.mm"
include "cuz.mm"
include "wss.mm"
include "1zzd.mm"
include "zsubcld.mm"
include "zred.mm"
include "nnaddcl.mm"
include "mp2an.mm"
include "a1i.mm"
include "nnred.mm"
include "zlem1lt.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "ltled.mm"
include "eluz.mm"
include "fzss2.mm"
include "sseld.mm"
include "crab.mm"
include "rabid.mm"
include "cr.mm"
include "cinf.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "ballotlemsup.mm"
include "wor.mm"
include "ltso.mm"
include "id.mm"
include "inflb.mm"
include "ballotlemi.mm"
include "breq2d.mm"
include "notbid.mm"
include "sylibrd.mm"
include "syl5bir.mm"
include "syland.mm"
include "imp.mm"
include "biid.mm"
include "sylnib.mm"
include "anassrs.mm"
include "pm2.65da.mm"
include "nrexdv.mm"

theorem ballotlemimin
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
  assert |- ( C e. ( O \ E ) -> -. E. k e. ( 1 ... ( ( I ` C ) - 1 ) ) ( ( F ` C ) ` k ) = 0 )

  proof
    cC
    cO
    cE
    cdif
    wcel
    #
    vk
    cv
    #
    cC
    cF
    cfv
    #
    cfv
    cc0
    wceq
    #
    vk
    c1
    cC
    cI
    cfv
    #
    c1
    cmin
    co
    #
    cfz
    co
    #
    @0
    @1
    @6
    wcel
    #
    wa
    #
    @3
    @1
    @4
    clt
    wbr
    #
    @8
    @9
    @3
    @8
    @9
    @1
    @5
    cle
    wbr
    #
    @7
    @10
    @0
    @1
    c1
    @5
    elfzle2
    adantl
    @7
    @1
    cz
    wcel
    @4
    cz
    wcel
    #
    @9
    @10
    wb
    @0
    @1
    c1
    @5
    elfzelz
    @0
    @4
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
    #
    wcel
    #
    @4
    cn
    wcel
    @0
    @14
    @4
    @2
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
    @12
    elfznn
    syl
    nnzd
    #
    @1
    @4
    zltlem1
    syl2anr
    mpbird
    adantr
    @0
    @7
    @3
    @9
    wn
    #
    @0
    @7
    @3
    wa
    #
    wa
    @9
    @9
    @0
    @18
    @17
    @0
    @7
    @1
    @13
    wcel
    #
    @3
    @17
    @0
    @6
    @13
    @1
    @0
    @12
    @5
    cuz
    cfv
    wcel
    #
    @6
    @13
    wss
    @0
    @20
    @5
    @12
    cle
    wbr
    #
    @0
    @5
    @12
    @0
    @5
    @0
    @4
    c1
    @16
    @0
    1zzd
    zsubcld
    #
    zred
    @0
    @12
    @12
    cn
    wcel
    #
    @0
    cM
    cn
    wcel
    cN
    cn
    wcel
    @23
    ballotth.m
    ballotth.n
    cM
    cN
    nnaddcl
    mp2an
    a1i
    #
    nnred
    @0
    @4
    @12
    cle
    wbr
    #
    @5
    @12
    clt
    wbr
    #
    @0
    @14
    @25
    @15
    @4
    c1
    @12
    elfzle2
    syl
    @0
    @11
    @12
    cz
    wcel
    #
    @25
    @26
    wb
    @16
    @0
    @12
    @24
    nnzd
    #
    @4
    @12
    zlem1lt
    syl2anc
    mpbid
    ltled
    @0
    @5
    cz
    wcel
    @27
    @20
    @21
    wb
    @22
    @28
    @5
    @12
    eluz
    syl2anc
    mpbird
    @5
    c1
    @12
    fzss2
    syl
    sseld
    @19
    @3
    wa
    @1
    @3
    vk
    @13
    crab
    #
    wcel
    #
    @0
    @17
    @3
    vk
    @13
    rabid
    @0
    @30
    @1
    @29
    cr
    clt
    cinf
    #
    clt
    wbr
    #
    wn
    #
    @17
    @0
    vw
    cv
    #
    vz
    cv
    #
    clt
    wbr
    wn
    vw
    @29
    wral
    @35
    @34
    clt
    wbr
    vy
    cv
    @34
    clt
    wbr
    vy
    @29
    wrex
    wi
    vw
    cr
    wral
    wa
    vz
    cr
    wrex
    #
    @30
    @33
    wi
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
    @36
    vz
    vw
    vy
    cr
    @29
    @1
    clt
    cr
    clt
    wor
    @36
    ltso
    a1i
    @36
    id
    inflb
    syl
    @0
    @9
    @32
    @0
    @4
    @31
    @1
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
    notbid
    sylibrd
    syl5bir
    syland
    imp
    @9
    biid
    sylnib
    anassrs
    pm2.65da
    nrexdv
end
