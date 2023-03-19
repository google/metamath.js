include "cur.mm"
include "cfv.mm"
include "cvsca.mm"
include "co.mm"
include "cbs.mm"
include "wcel.mm"
include "wceq.mm"
include "crg.mm"
include "clmod.mm"
include "lmodring.mm"
include "syl.mm"
include "eqid.mm"
include "ringidcl.mm"
include "asclval.mm"
include "lmodvs1.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem ascl1
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cW: class W
  let vk: setvar k
  let vx: setvar x
  assume ascl0.a: |- A = ( algSc ` W )
  assume ascl0.f: |- F = ( Scalar ` W )
  assume ascl0.l: |- ( ph -> W e. LMod )
  assume ascl0.r: |- ( ph -> W e. Ring )


  assert |- ( ph -> ( A ` ( 1r ` F ) ) = ( 1r ` W ) )

  proof
    wph
    cF
    cur
    cfv
    #
    cA
    cfv
    #
    @0
    cW
    cur
    cfv
    #
    cW
    cvsca
    cfv
    #
    co
    #
    @2
    wph
    @0
    cF
    cbs
    cfv
    #
    wcel
    #
    @1
    @4
    wceq
    wph
    cF
    crg
    wcel
    #
    @6
    wph
    cW
    clmod
    wcel
    #
    @7
    ascl0.l
    cF
    cW
    ascl0.f
    lmodring
    syl
    @5
    cF
    @0
    @5
    eqid
    #
    @0
    eqid
    #
    ringidcl
    syl
    cA
    @3
    @2
    cF
    @5
    cW
    @0
    ascl0.a
    ascl0.f
    @9
    @3
    eqid
    #
    @2
    eqid
    #
    asclval
    syl
    wph
    @8
    @2
    cW
    cbs
    cfv
    #
    wcel
    #
    @4
    @2
    wceq
    ascl0.l
    wph
    cW
    crg
    wcel
    @14
    ascl0.r
    @13
    cW
    @2
    @13
    eqid
    #
    @12
    ringidcl
    syl
    @3
    @0
    cF
    @13
    cW
    @2
    @15
    ascl0.f
    @11
    @10
    lmodvs1
    syl2anc
    eqtrd
end
