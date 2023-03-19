include "co.mm"
include "wceq.mm"
include "wa.mm"
include "csn.mm"
include "cfv.mm"
include "ccntz.mm"
include "eqid.mm"
include "clmod.mm"
include "wcel.mm"
include "csubg.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "eldifad.mm"
include "lspsnsubg.mm"
include "syl2anc.mm"
include "lspdisj2.mm"
include "cabl.mm"
include "lmodabl.mm"
include "ablcntzd.mm"
include "lspsneli.mm"
include "subgdisjb.mm"
include "mpbid.mm"
include "cdif.mm"
include "wne.mm"
include "eldifsni.mm"
include "lvecvscan2.mm"
include "anbi12d.mm"

theorem lvecindp2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume lvecindp2.v: |- V = ( Base ` W )
  assume lvecindp2.p: |- .+ = ( +g ` W )
  assume lvecindp2.f: |- F = ( Scalar ` W )
  assume lvecindp2.k: |- K = ( Base ` F )
  assume lvecindp2.t: |- .x. = ( .s ` W )
  assume lvecindp2.o: |- .0. = ( 0g ` W )
  assume lvecindp2.n: |- N = ( LSpan ` W )
  assume lvecindp2.w: |- ( ph -> W e. LVec )
  assume lvecindp2.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume lvecindp2.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume lvecindp2.a: |- ( ph -> A e. K )
  assume lvecindp2.b: |- ( ph -> B e. K )
  assume lvecindp2.c: |- ( ph -> C e. K )
  assume lvecindp2.d: |- ( ph -> D e. K )
  assume lvecindp2.q: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )
  assume lvecindp2.e: |- ( ph -> ( ( A .x. X ) .+ ( B .x. Y ) ) = ( ( C .x. X ) .+ ( D .x. Y ) ) )


  assert |- ( ph -> ( A = C /\ B = D ) )

  proof
    wph
    cA
    cX
    c.x
    co
    #
    cC
    cX
    c.x
    co
    #
    wceq
    #
    cB
    cY
    c.x
    co
    #
    cD
    cY
    c.x
    co
    #
    wceq
    #
    wa
    #
    cA
    cC
    wceq
    #
    cB
    cD
    wceq
    #
    wa
    wph
    @0
    @3
    c.pl
    co
    @1
    @4
    c.pl
    co
    wceq
    @6
    lvecindp2.e
    wph
    @0
    @3
    @1
    @4
    c.pl
    cX
    csn
    cN
    cfv
    #
    cY
    csn
    cN
    cfv
    #
    cW
    c.0
    cW
    ccntz
    cfv
    #
    lvecindp2.p
    lvecindp2.o
    @11
    eqid
    #
    wph
    cW
    clmod
    wcel
    #
    cX
    cV
    wcel
    @9
    cW
    csubg
    cfv
    #
    wcel
    wph
    cW
    clvec
    wcel
    @13
    lvecindp2.w
    cW
    lveclmod
    syl
    #
    wph
    cX
    cV
    c.0
    csn
    #
    lvecindp2.x
    eldifad
    #
    cN
    cV
    cW
    cX
    lvecindp2.v
    lvecindp2.n
    lspsnsubg
    syl2anc
    #
    wph
    @13
    cY
    cV
    wcel
    @10
    @14
    wcel
    @15
    wph
    cY
    cV
    @16
    lvecindp2.y
    eldifad
    #
    cN
    cV
    cW
    cY
    lvecindp2.v
    lvecindp2.n
    lspsnsubg
    syl2anc
    #
    wph
    cN
    cV
    cW
    cX
    cY
    c.0
    lvecindp2.v
    lvecindp2.o
    lvecindp2.n
    lvecindp2.w
    @17
    @19
    lvecindp2.q
    lspdisj2
    wph
    @9
    @10
    cW
    @11
    @12
    wph
    @13
    cW
    cabl
    wcel
    @15
    cW
    lmodabl
    syl
    @18
    @20
    ablcntzd
    wph
    cA
    c.x
    cF
    cK
    cN
    cV
    cW
    cX
    lvecindp2.v
    lvecindp2.t
    lvecindp2.f
    lvecindp2.k
    lvecindp2.n
    @15
    lvecindp2.a
    @17
    lspsneli
    wph
    cC
    c.x
    cF
    cK
    cN
    cV
    cW
    cX
    lvecindp2.v
    lvecindp2.t
    lvecindp2.f
    lvecindp2.k
    lvecindp2.n
    @15
    lvecindp2.c
    @17
    lspsneli
    wph
    cB
    c.x
    cF
    cK
    cN
    cV
    cW
    cY
    lvecindp2.v
    lvecindp2.t
    lvecindp2.f
    lvecindp2.k
    lvecindp2.n
    @15
    lvecindp2.b
    @19
    lspsneli
    wph
    cD
    c.x
    cF
    cK
    cN
    cV
    cW
    cY
    lvecindp2.v
    lvecindp2.t
    lvecindp2.f
    lvecindp2.k
    lvecindp2.n
    @15
    lvecindp2.d
    @19
    lspsneli
    subgdisjb
    mpbid
    wph
    @2
    @7
    @5
    @8
    wph
    cA
    cC
    c.x
    cF
    cK
    cV
    cW
    cX
    c.0
    lvecindp2.v
    lvecindp2.t
    lvecindp2.f
    lvecindp2.k
    lvecindp2.o
    lvecindp2.w
    lvecindp2.a
    lvecindp2.c
    @17
    wph
    cX
    cV
    @16
    cdif
    #
    wcel
    cX
    c.0
    wne
    lvecindp2.x
    cX
    cV
    c.0
    eldifsni
    syl
    lvecvscan2
    wph
    cB
    cD
    c.x
    cF
    cK
    cV
    cW
    cY
    c.0
    lvecindp2.v
    lvecindp2.t
    lvecindp2.f
    lvecindp2.k
    lvecindp2.o
    lvecindp2.w
    lvecindp2.b
    lvecindp2.d
    @19
    wph
    cY
    @21
    wcel
    cY
    c.0
    wne
    lvecindp2.y
    cY
    cV
    c.0
    eldifsni
    syl
    lvecvscan2
    anbi12d
    mpbid
end
