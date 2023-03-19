include "cfv.mm"
include "ces.mm"
include "co.mm"
include "cmap.mm"
include "csn.mm"
include "cxp.mm"
include "cress.mm"
include "cmpl.mm"
include "cascl.mm"
include "ccrg.mm"
include "wcel.mm"
include "wceq.mm"
include "ressid.mm"
include "eqcomd.mm"
include "syl.mm"
include "oveq2d.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "eqid.mm"
include "crg.mm"
include "csubrg.mm"
include "crngring.mm"
include "subrgid.mm"
include "3syl.mm"
include "wss.mm"
include "subrgss.mm"
include "sseldd.mm"
include "evlssca.mm"
include "eqtrd.mm"
include "evlval.mm"
include "a1i.mm"
include "3eqtr4rd.mm"

theorem evlsscasrng
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cI: class I
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  assume evlsscasrng.q: |- Q = ( ( I evalSub S ) ` R )
  assume evlsscasrng.o: |- O = ( I eval S )
  assume evlsscasrng.w: |- W = ( I mPoly U )
  assume evlsscasrng.u: |- U = ( S |`s R )
  assume evlsscasrng.p: |- P = ( I mPoly S )
  assume evlsscasrng.b: |- B = ( Base ` S )
  assume evlsscasrng.a: |- A = ( algSc ` W )
  assume evlsscasrng.c: |- C = ( algSc ` P )
  assume evlsscasrng.i: |- ( ph -> I e. V )
  assume evlsscasrng.s: |- ( ph -> S e. CRing )
  assume evlsscasrng.r: |- ( ph -> R e. ( SubRing ` S ) )
  assume evlsscasrng.x: |- ( ph -> X e. R )


  assert |- ( ph -> ( Q ` ( A ` X ) ) = ( O ` ( C ` X ) ) )

  proof
    wph
    cX
    cC
    cfv
    #
    cB
    cI
    cS
    ces
    co
    cfv
    #
    cfv
    #
    cB
    cI
    cmap
    co
    cX
    csn
    cxp
    #
    @0
    cO
    cfv
    cX
    cA
    cfv
    cQ
    cfv
    wph
    @2
    cX
    cI
    cS
    cB
    cress
    co
    #
    cmpl
    co
    #
    cascl
    cfv
    #
    cfv
    #
    @1
    cfv
    @3
    wph
    @0
    @7
    @1
    wph
    cX
    cC
    @6
    wph
    cC
    cP
    cascl
    cfv
    @6
    evlsscasrng.c
    wph
    cP
    @5
    cascl
    wph
    cP
    cI
    cS
    cmpl
    co
    @5
    evlsscasrng.p
    wph
    cS
    @4
    cI
    cmpl
    wph
    cS
    ccrg
    wcel
    #
    cS
    @4
    wceq
    evlsscasrng.s
    @8
    @4
    cS
    cB
    cS
    ccrg
    evlsscasrng.b
    ressid
    eqcomd
    syl
    oveq2d
    syl5eq
    fveq2d
    syl5eq
    fveq1d
    fveq2d
    wph
    @6
    cB
    @1
    cB
    cS
    @4
    cI
    cV
    @5
    cX
    @1
    eqid
    @5
    eqid
    @4
    eqid
    evlsscasrng.b
    @6
    eqid
    evlsscasrng.i
    evlsscasrng.s
    wph
    @8
    cS
    crg
    wcel
    cB
    cS
    csubrg
    cfv
    #
    wcel
    evlsscasrng.s
    cS
    crngring
    cB
    cS
    evlsscasrng.b
    subrgid
    3syl
    wph
    cR
    cB
    cX
    wph
    cR
    @9
    wcel
    cR
    cB
    wss
    evlsscasrng.r
    cR
    cB
    cS
    evlsscasrng.b
    subrgss
    syl
    evlsscasrng.x
    sseldd
    evlssca
    eqtrd
    wph
    @0
    cO
    @1
    cO
    @1
    wceq
    wph
    cB
    cO
    cS
    cI
    evlsscasrng.o
    evlsscasrng.b
    evlval
    a1i
    fveq1d
    wph
    cA
    cB
    cQ
    cR
    cS
    cU
    cI
    cV
    cW
    cX
    evlsscasrng.q
    evlsscasrng.w
    evlsscasrng.u
    evlsscasrng.b
    evlsscasrng.a
    evlsscasrng.i
    evlsscasrng.s
    evlsscasrng.r
    evlsscasrng.x
    evlssca
    3eqtr4rd
end
