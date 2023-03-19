include "cdif.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "wrex.mm"
include "eldif.mm"
include "clt.mm"
include "wral.mm"
include "wo.mm"
include "wi.mm"
include "df-or.mm"
include "pm3.24.mm"
include "a1bi.mm"
include "bitr4i.mm"
include "ballotleme.mm"
include "notbii.mm"
include "anbi2i.mm"
include "ianor.mm"
include "andi.mm"
include "3bitri.mm"
include "cr.mm"
include "wss.mm"
include "0p1e1.mm"
include "oveq1i.mm"
include "cz.mm"
include "0z.mm"
include "fzp1ss.mm"
include "ax-mp.mm"
include "eqsstr3i.mm"
include "a1i.mm"
include "sseld.mm"
include "imdistani.mm"
include "wsb.mm"
include "simpl.mm"
include "elfzelz.mm"
include "adantl.mm"
include "ballotlemfelz.mm"
include "zred.mm"
include "sbimi.mm"
include "sban.mm"
include "nfv.mm"
include "sbf.mm"
include "clelsb3.mm"
include "anbi12i.mm"
include "bitri.mm"
include "weq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "sbie.mm"
include "3imtr3i.mm"
include "syl.mm"
include "0red.mm"
include "lenltd.mm"
include "rexbidva.mm"
include "rexnal.mm"
include "syl6bb.mm"
include "pm5.32i.mm"
include "3bitr4i.mm"

theorem ballotlemodife
  let vx: setvar x
  let cC: class C
  let cP: class P
  let vi: setvar i
  let cE: class E
  let cF: class F
  let cM: class M
  let cN: class N
  let cO: class O
  let vc: setvar c
  let vj: setvar j
  let vk: setvar k
  assume ballotth.m: |- M e. NN
  assume ballotth.n: |- N e. NN
  assume ballotth.o: |- O = { c e. ~P ( 1 ... ( M + N ) ) | ( # ` c ) = M }
  assume ballotth.p: |- P = ( x e. ~P O |-> ( ( # ` x ) / ( # ` O ) ) )
  assume ballotth.f: |- F = ( c e. O |-> ( i e. ZZ |-> ( ( # ` ( ( 1 ... i ) i^i c ) ) - ( # ` ( ( 1 ... i ) \ c ) ) ) ) )
  assume ballotth.e: |- E = { c e. O | A. i e. ( 1 ... ( M + N ) ) 0 < ( ( F ` c ) ` i ) }

  disjoint C i
  disjoint c i
  disjoint F c
  disjoint F i
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
  disjoint i j
  disjoint C j
  disjoint F j
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint M k
  disjoint N k
  disjoint O k
  disjoint F j
  disjoint F k
  assert |- ( C e. ( O \ E ) <-> ( C e. O /\ E. i e. ( 1 ... ( M + N ) ) ( ( F ` C ) ` i ) <_ 0 ) )

  proof
    cC
    cO
    cE
    cdif
    wcel
    cC
    cO
    wcel
    #
    cC
    cE
    wcel
    #
    wn
    #
    wa
    #
    @0
    vi
    cv
    #
    cC
    cF
    cfv
    #
    cfv
    #
    cc0
    cle
    wbr
    #
    vi
    c1
    cM
    cN
    caddc
    co
    #
    cfz
    co
    #
    wrex
    #
    wa
    #
    cC
    cO
    cE
    eldif
    @0
    @0
    wn
    #
    wa
    #
    @0
    cc0
    @6
    clt
    wbr
    #
    vi
    @9
    wral
    #
    wn
    #
    wa
    #
    wo
    #
    @17
    @3
    @11
    @18
    @13
    wn
    #
    @17
    wi
    @17
    @13
    @17
    df-or
    @19
    @17
    @0
    pm3.24
    a1bi
    bitr4i
    @3
    @0
    @0
    @15
    wa
    #
    wn
    #
    wa
    @0
    @12
    @16
    wo
    #
    wa
    @18
    @2
    @21
    @0
    @1
    @20
    vx
    cC
    cP
    vi
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
    ballotleme
    notbii
    anbi2i
    @21
    @22
    @0
    @0
    @15
    ianor
    anbi2i
    @0
    @12
    @16
    andi
    3bitri
    @0
    @10
    @16
    @0
    @10
    @14
    wn
    #
    vi
    @9
    wrex
    @16
    @0
    @7
    @23
    vi
    @9
    @0
    @4
    @9
    wcel
    #
    wa
    #
    @6
    cc0
    @25
    @0
    @4
    cc0
    @8
    cfz
    co
    #
    wcel
    #
    wa
    #
    @6
    cr
    wcel
    #
    @0
    @24
    @27
    @0
    @9
    @26
    @4
    @9
    @26
    wss
    @0
    @9
    cc0
    c1
    caddc
    co
    #
    @8
    cfz
    co
    #
    @26
    @30
    c1
    @8
    cfz
    0p1e1
    oveq1i
    cc0
    cz
    wcel
    @31
    @26
    wss
    0z
    cc0
    @8
    fzp1ss
    ax-mp
    eqsstr3i
    a1i
    sseld
    imdistani
    @0
    vj
    cv
    #
    @26
    wcel
    #
    wa
    #
    vj
    vi
    wsb
    #
    @32
    @5
    cfv
    #
    cr
    wcel
    #
    vj
    vi
    wsb
    @28
    @29
    @34
    @37
    vj
    vi
    @34
    @36
    @34
    vx
    cC
    cP
    vi
    cF
    @32
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
    @33
    simpl
    @33
    @32
    cz
    wcel
    @0
    @32
    cc0
    @8
    elfzelz
    adantl
    ballotlemfelz
    zred
    sbimi
    @35
    @0
    vj
    vi
    wsb
    #
    @33
    vj
    vi
    wsb
    #
    wa
    @28
    @0
    @33
    vj
    vi
    sban
    @38
    @0
    @39
    @27
    @0
    vj
    vi
    @0
    vj
    nfv
    sbf
    vi
    vj
    @26
    clelsb3
    anbi12i
    bitri
    @37
    @29
    vj
    vi
    @29
    vj
    nfv
    vj
    vi
    weq
    @36
    @6
    cr
    @32
    @4
    @5
    fveq2
    eleq1d
    sbie
    3imtr3i
    syl
    @25
    0red
    lenltd
    rexbidva
    @14
    vi
    @9
    rexnal
    syl6bb
    pm5.32i
    3bitr4i
    bitri
end
