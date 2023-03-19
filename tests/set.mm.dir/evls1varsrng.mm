include "cfv.mm"
include "cid.mm"
include "cres.mm"
include "evls1var.mm"
include "ces1.mm"
include "co.mm"
include "cress.mm"
include "cv1.mm"
include "wceq.mm"
include "evl1fval1.mm"
include "a1i.mm"
include "fveq1d.mm"
include "eqid.mm"
include "subrgvr1.mm"
include "ccrg.mm"
include "wcel.mm"
include "ressid.mm"
include "syl.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "3eqtr2d.mm"
include "crg.mm"
include "csubrg.mm"
include "crngring.mm"
include "subrgid.mm"
include "3syl.mm"
include "3eqtrrd.mm"
include "eqtrd.mm"

theorem evls1varsrng
  let wph: wff ph
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cO: class O
  let cV: class V
  assume evls1varsrng.q: |- Q = ( S evalSub1 R )
  assume evls1varsrng.o: |- O = ( eval1 ` S )
  assume evls1varsrng.v: |- V = ( var1 ` U )
  assume evls1varsrng.u: |- U = ( S |`s R )
  assume evls1varsrng.b: |- B = ( Base ` S )
  assume evls1varsrng.s: |- ( ph -> S e. CRing )
  assume evls1varsrng.r: |- ( ph -> R e. ( SubRing ` S ) )


  assert |- ( ph -> ( Q ` V ) = ( O ` V ) )

  proof
    wph
    cV
    cQ
    cfv
    cid
    cB
    cres
    #
    cV
    cO
    cfv
    #
    wph
    cB
    cQ
    cR
    cS
    cU
    cV
    evls1varsrng.q
    evls1varsrng.v
    evls1varsrng.u
    evls1varsrng.b
    evls1varsrng.s
    evls1varsrng.r
    evls1var
    wph
    @1
    cV
    cS
    cB
    ces1
    co
    #
    cfv
    cS
    cB
    cress
    co
    #
    cv1
    cfv
    #
    @2
    cfv
    @0
    wph
    cV
    cO
    @2
    cO
    @2
    wceq
    wph
    cB
    cO
    cS
    evls1varsrng.o
    evls1varsrng.b
    evl1fval1
    a1i
    fveq1d
    wph
    cV
    @4
    @2
    wph
    cV
    cU
    cv1
    cfv
    #
    cS
    cv1
    cfv
    #
    @4
    cV
    @5
    wceq
    wph
    evls1varsrng.v
    a1i
    wph
    cS
    cR
    cU
    @6
    @6
    eqid
    evls1varsrng.r
    evls1varsrng.u
    subrgvr1
    wph
    cS
    @3
    cv1
    wph
    @3
    cS
    wph
    cS
    ccrg
    wcel
    #
    @3
    cS
    wceq
    evls1varsrng.s
    cB
    cS
    ccrg
    evls1varsrng.b
    ressid
    syl
    eqcomd
    fveq2d
    3eqtr2d
    fveq2d
    wph
    cB
    @2
    cB
    cS
    @3
    @4
    @2
    eqid
    @4
    eqid
    @3
    eqid
    evls1varsrng.b
    evls1varsrng.s
    wph
    @7
    cS
    crg
    wcel
    cB
    cS
    csubrg
    cfv
    wcel
    evls1varsrng.s
    cS
    crngring
    cB
    cS
    evls1varsrng.b
    subrgid
    3syl
    evls1var
    3eqtrrd
    eqtrd
end
