include "co.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "frlmvscafval.mm"
include "fveq1d.mm"
include "wfn.mm"
include "wcel.mm"
include "wceq.mm"
include "fnconstg.mm"
include "syl.mm"
include "wf.mm"
include "frlmbasf.mm"
include "syl2anc.mm"
include "ffn.mm"
include "fnfvof.mm"
include "syl22anc.mm"
include "fvconst2g.mm"
include "oveq1d.mm"
include "3eqtrd.mm"

theorem frlmvscaval
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let cI: class I
  let cJ: class J
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  assume frlmvscaval.y: |- Y = ( R freeLMod I )
  assume frlmvscaval.b: |- B = ( Base ` Y )
  assume frlmvscaval.k: |- K = ( Base ` R )
  assume frlmvscaval.i: |- ( ph -> I e. W )
  assume frlmvscaval.a: |- ( ph -> A e. K )
  assume frlmvscaval.x: |- ( ph -> X e. B )
  assume frlmvscaval.j: |- ( ph -> J e. I )
  assume frlmvscaval.v: |- .xb = ( .s ` Y )
  assume frlmvscaval.t: |- .x. = ( .r ` R )


  assert |- ( ph -> ( ( A .xb X ) ` J ) = ( A .x. ( X ` J ) ) )

  proof
    wph
    cJ
    cA
    cX
    c.xb
    co
    #
    cfv
    cJ
    cI
    cA
    csn
    cxp
    #
    cX
    c.x
    cof
    co
    #
    cfv
    #
    cJ
    @1
    cfv
    #
    cJ
    cX
    cfv
    #
    c.x
    co
    #
    cA
    @5
    c.x
    co
    wph
    cJ
    @0
    @2
    wph
    cA
    cB
    cR
    c.xb
    c.x
    cI
    cK
    cW
    cX
    cY
    frlmvscaval.y
    frlmvscaval.b
    frlmvscaval.k
    frlmvscaval.i
    frlmvscaval.a
    frlmvscaval.x
    frlmvscaval.v
    frlmvscaval.t
    frlmvscafval
    fveq1d
    wph
    @1
    cI
    wfn
    #
    cX
    cI
    wfn
    #
    cI
    cW
    wcel
    #
    cJ
    cI
    wcel
    #
    @3
    @6
    wceq
    wph
    cA
    cK
    wcel
    #
    @7
    frlmvscaval.a
    cI
    cA
    cK
    fnconstg
    syl
    wph
    cI
    cK
    cX
    wf
    #
    @8
    wph
    @9
    cX
    cB
    wcel
    @12
    frlmvscaval.i
    frlmvscaval.x
    cB
    cR
    cY
    cI
    cK
    cW
    cX
    frlmvscaval.y
    frlmvscaval.k
    frlmvscaval.b
    frlmbasf
    syl2anc
    cI
    cK
    cX
    ffn
    syl
    frlmvscaval.i
    frlmvscaval.j
    cI
    c.x
    @1
    cX
    cW
    cJ
    fnfvof
    syl22anc
    wph
    @4
    cA
    @5
    c.x
    wph
    @11
    @10
    @4
    cA
    wceq
    frlmvscaval.a
    frlmvscaval.j
    cI
    cA
    cJ
    cK
    fvconst2g
    syl2anc
    oveq1d
    3eqtrd
end
