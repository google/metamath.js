include "wcel.mm"
include "c1.mm"
include "wn.mm"
include "wa.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "wral.mm"
include "wrex.mm"
include "cuz.mm"
include "cn.mm"
include "nnaddcl.mm"
include "mp2an.mm"
include "elnnuz.mm"
include "mpbi.mm"
include "eluzfz1.mm"
include "ax-mp.mm"
include "cmin.mm"
include "cle.mm"
include "0le1.mm"
include "0re.mm"
include "1re.mm"
include "lenlti.mm"
include "cr.mm"
include "wb.mm"
include "ltsub13.mm"
include "mp3an.mm"
include "0m0e0.mm"
include "breq2i.mm"
include "bitri.mm"
include "mtbir.mm"
include "1m1e0.mm"
include "fveq2i.mm"
include "ballotlemfval0.mm"
include "syl5eq.mm"
include "oveq1d.mm"
include "breq2d.mm"
include "mtbiri.mm"
include "adantr.mm"
include "wceq.mm"
include "wi.mm"
include "simpl.mm"
include "1nn.mm"
include "a1i.mm"
include "ballotlemfp1.mm"
include "simpld.mm"
include "mpan2.mm"
include "imp.mm"
include "mtbird.mm"
include "fveq2.mm"
include "notbid.mm"
include "rspcev.mm"
include "sylancr.mm"
include "rexnal.mm"
include "sylib.mm"
include "ballotleme.mm"
include "simprbi.mm"
include "nsyl.mm"
include "ex.mm"

theorem ballotlem4
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
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint M k
  disjoint N k
  disjoint O k
  disjoint F j
  disjoint F k
  assert |- ( C e. O -> ( -. 1 e. C -> -. C e. E ) )

  proof
    cC
    cO
    wcel
    #
    c1
    cC
    wcel
    #
    wn
    #
    cC
    cE
    wcel
    #
    wn
    @0
    @2
    wa
    #
    cc0
    vi
    cv
    #
    cC
    cF
    cfv
    #
    cfv
    #
    clt
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
    wral
    #
    @3
    @4
    @8
    wn
    #
    vi
    @10
    wrex
    #
    @11
    wn
    @4
    c1
    @10
    wcel
    #
    cc0
    c1
    @6
    cfv
    #
    clt
    wbr
    #
    wn
    #
    @13
    @9
    c1
    cuz
    cfv
    wcel
    #
    @14
    @9
    cn
    wcel
    #
    @18
    cM
    cn
    wcel
    cN
    cn
    wcel
    @19
    ballotth.m
    ballotth.n
    cM
    cN
    nnaddcl
    mp2an
    @9
    elnnuz
    mpbi
    c1
    @9
    eluzfz1
    ax-mp
    #
    @4
    @16
    cc0
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
    clt
    wbr
    #
    @0
    @24
    wn
    @2
    @0
    @24
    cc0
    cc0
    c1
    cmin
    co
    #
    clt
    wbr
    #
    @26
    c1
    cc0
    clt
    wbr
    #
    cc0
    c1
    cle
    wbr
    @27
    wn
    0le1
    cc0
    c1
    0re
    1re
    lenlti
    mpbi
    @26
    c1
    cc0
    cc0
    cmin
    co
    #
    clt
    wbr
    #
    @27
    cc0
    cr
    wcel
    #
    @30
    c1
    cr
    wcel
    @26
    @29
    wb
    0re
    0re
    1re
    cc0
    cc0
    c1
    ltsub13
    mp3an
    @28
    cc0
    c1
    clt
    0m0e0
    breq2i
    bitri
    mtbir
    @0
    @23
    @25
    cc0
    clt
    @0
    @22
    cc0
    c1
    cmin
    @0
    @22
    cc0
    @6
    cfv
    cc0
    @21
    cc0
    @6
    1m1e0
    fveq2i
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
    syl5eq
    oveq1d
    breq2d
    mtbiri
    adantr
    @4
    @15
    @23
    cc0
    clt
    @0
    @2
    @15
    @23
    wceq
    #
    @0
    @14
    @2
    @31
    wi
    #
    @20
    @0
    @14
    wa
    #
    @32
    @1
    @15
    @22
    c1
    caddc
    co
    wceq
    wi
    @33
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
    @0
    @14
    simpl
    c1
    cn
    wcel
    @33
    1nn
    a1i
    ballotlemfp1
    simpld
    mpan2
    imp
    breq2d
    mtbird
    @12
    @17
    vi
    c1
    @10
    @5
    c1
    wceq
    #
    @8
    @16
    @34
    @7
    @15
    cc0
    clt
    @5
    c1
    @6
    fveq2
    breq2d
    notbid
    rspcev
    sylancr
    @8
    vi
    @10
    rexnal
    sylib
    @3
    @0
    @11
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
    simprbi
    nsyl
    ex
end
