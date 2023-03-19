include "cfv.mm"
include "ces1.mm"
include "co.mm"
include "csn.mm"
include "cxp.mm"
include "cress.mm"
include "cpl1.mm"
include "cascl.mm"
include "ccrg.mm"
include "wcel.mm"
include "wceq.mm"
include "ressid.mm"
include "eqcomd.mm"
include "syl.mm"
include "fveq2d.mm"
include "syl5eq.mm"
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
include "evls1sca.mm"
include "eqtrd.mm"
include "evl1fval1.mm"
include "a1i.mm"
include "3eqtr4rd.mm"

theorem evls1scasrng
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cO: class O
  let cW: class W
  let cX: class X
  assume evls1scasrng.q: |- Q = ( S evalSub1 R )
  assume evls1scasrng.o: |- O = ( eval1 ` S )
  assume evls1scasrng.w: |- W = ( Poly1 ` U )
  assume evls1scasrng.u: |- U = ( S |`s R )
  assume evls1scasrng.p: |- P = ( Poly1 ` S )
  assume evls1scasrng.b: |- B = ( Base ` S )
  assume evls1scasrng.a: |- A = ( algSc ` W )
  assume evls1scasrng.c: |- C = ( algSc ` P )
  assume evls1scasrng.s: |- ( ph -> S e. CRing )
  assume evls1scasrng.r: |- ( ph -> R e. ( SubRing ` S ) )
  assume evls1scasrng.x: |- ( ph -> X e. R )


  assert |- ( ph -> ( Q ` ( A ` X ) ) = ( O ` ( C ` X ) ) )

  proof
    wph
    cX
    cC
    cfv
    #
    cS
    cB
    ces1
    co
    #
    cfv
    #
    cB
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
    cS
    cB
    cress
    co
    #
    cpl1
    cfv
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
    evls1scasrng.c
    wph
    cP
    @5
    cascl
    wph
    cP
    cS
    cpl1
    cfv
    @5
    evls1scasrng.p
    wph
    cS
    @4
    cpl1
    wph
    cS
    ccrg
    wcel
    #
    cS
    @4
    wceq
    evls1scasrng.s
    @8
    @4
    cS
    cB
    cS
    ccrg
    evls1scasrng.b
    ressid
    eqcomd
    syl
    fveq2d
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
    @5
    cX
    @1
    eqid
    @5
    eqid
    @4
    eqid
    evls1scasrng.b
    @6
    eqid
    evls1scasrng.s
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
    evls1scasrng.s
    cS
    crngring
    cB
    cS
    evls1scasrng.b
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
    evls1scasrng.r
    cR
    cB
    cS
    evls1scasrng.b
    subrgss
    syl
    evls1scasrng.x
    sseldd
    evls1sca
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
    evls1scasrng.o
    evls1scasrng.b
    evl1fval1
    a1i
    fveq1d
    wph
    cA
    cB
    cQ
    cR
    cS
    cU
    cW
    cX
    evls1scasrng.q
    evls1scasrng.w
    evls1scasrng.u
    evls1scasrng.b
    evls1scasrng.a
    evls1scasrng.s
    evls1scasrng.r
    evls1scasrng.x
    evls1sca
    3eqtr4rd
end
