include "co.mm"
include "crglmod.mm"
include "cfv.mm"
include "cpws.mm"
include "cvsca.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "cress.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "frlmrcl.mm"
include "syl.mm"
include "frlmpws.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "eqid.mm"
include "ressvsca.mm"
include "ax-mp.mm"
include "3eqtr4g.mm"
include "oveqd.mm"
include "csca.mm"
include "cmulr.mm"
include "rlmvsca.mm"
include "eqtri.mm"
include "fvexd.mm"
include "rlmsca.mm"
include "syl5eq.mm"
include "eleqtrd.mm"
include "ressbasss.mm"
include "syl6eqss.mm"
include "sseldd.mm"
include "pwsvscafval.mm"
include "eqtrd.mm"

theorem frlmvscafval
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let cI: class I
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  assume frlmvscafval.y: |- Y = ( R freeLMod I )
  assume frlmvscafval.b: |- B = ( Base ` Y )
  assume frlmvscafval.k: |- K = ( Base ` R )
  assume frlmvscafval.i: |- ( ph -> I e. W )
  assume frlmvscafval.a: |- ( ph -> A e. K )
  assume frlmvscafval.x: |- ( ph -> X e. B )
  assume frlmvscafval.v: |- .xb = ( .s ` Y )
  assume frlmvscafval.t: |- .x. = ( .r ` R )


  assert |- ( ph -> ( A .xb X ) = ( ( I X. { A } ) oF .x. X ) )

  proof
    wph
    cA
    cX
    c.xb
    co
    cA
    cX
    cR
    crglmod
    cfv
    #
    cI
    cpws
    co
    #
    cvsca
    cfv
    #
    co
    cI
    cA
    csn
    cxp
    cX
    c.x
    cof
    co
    wph
    c.xb
    @2
    cA
    cX
    wph
    cY
    cvsca
    cfv
    @1
    cB
    cress
    co
    #
    cvsca
    cfv
    #
    c.xb
    @2
    wph
    cY
    @3
    cvsca
    wph
    cR
    cvv
    wcel
    #
    cI
    cW
    wcel
    cY
    @3
    wceq
    wph
    cX
    cB
    wcel
    @5
    frlmvscafval.x
    cB
    cR
    cY
    cI
    cX
    frlmvscafval.y
    frlmvscafval.b
    frlmrcl
    syl
    #
    frlmvscafval.i
    cB
    cR
    cY
    cI
    cvv
    cW
    frlmvscafval.y
    frlmvscafval.b
    frlmpws
    syl2anc
    #
    fveq2d
    frlmvscafval.v
    cB
    cvv
    wcel
    @2
    @4
    wceq
    cB
    cY
    cbs
    cfv
    #
    cvv
    frlmvscafval.b
    cY
    cbs
    fvex
    eqeltri
    cB
    @2
    @1
    @3
    cvv
    @3
    eqid
    #
    @2
    eqid
    #
    ressvsca
    ax-mp
    3eqtr4g
    oveqd
    wph
    cA
    @1
    cbs
    cfv
    #
    @0
    @2
    c.x
    @0
    csca
    cfv
    #
    cI
    @12
    cbs
    cfv
    #
    cvv
    cW
    cX
    @1
    @1
    eqid
    @11
    eqid
    #
    c.x
    cR
    cmulr
    cfv
    @0
    cvsca
    cfv
    frlmvscafval.t
    cR
    rlmvsca
    eqtri
    @10
    @12
    eqid
    @13
    eqid
    wph
    cR
    crglmod
    fvexd
    frlmvscafval.i
    wph
    cA
    cK
    @13
    frlmvscafval.a
    wph
    cK
    cR
    cbs
    cfv
    @13
    frlmvscafval.k
    wph
    cR
    @12
    cbs
    wph
    @5
    cR
    @12
    wceq
    @6
    cR
    cvv
    rlmsca
    syl
    fveq2d
    syl5eq
    eleqtrd
    wph
    cB
    @11
    cX
    wph
    cB
    @3
    cbs
    cfv
    #
    @11
    wph
    cB
    @8
    @15
    frlmvscafval.b
    wph
    cY
    @3
    cbs
    @7
    fveq2d
    syl5eq
    cB
    @11
    @3
    @1
    @9
    @14
    ressbasss
    syl6eqss
    frlmvscafval.x
    sseldd
    pwsvscafval
    eqtrd
end
