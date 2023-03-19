include "cop.mm"
include "cdv.mm"
include "co.mm"
include "wcel.mm"
include "cnt.mm"
include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cmin.mm"
include "cdiv.mm"
include "cmpt.mm"
include "climc.mm"
include "cxp.mm"
include "ciun.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "cc.mm"
include "wss.mm"
include "wf.mm"
include "dvfval.mm"
include "syl3anc.mm"
include "simpld.mm"
include "eleq2d.mm"
include "df-br.mm"
include "bicomi.mm"
include "sneq.mm"
include "difeq2d.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "mpteq12dv.mm"
include "syl6eqr.mm"
include "id.mm"
include "opeliunxp2.mm"
include "3bitr3g.mm"

theorem eldv
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let cK: class K
  let vf: setvar f
  let vs: setvar s
  let vx: setvar x
  assume dvval.t: |- T = ( K |`t S )
  assume dvval.k: |- K = ( TopOpen ` CCfld )
  assume eldv.g: |- G = ( z e. ( A \ { B } ) |-> ( ( ( F ` z ) - ( F ` B ) ) / ( z - B ) ) )
  assume eldv.s: |- ( ph -> S C_ CC )
  assume eldv.f: |- ( ph -> F : A --> CC )
  assume eldv.a: |- ( ph -> A C_ S )

  disjoint A z
  disjoint B z
  disjoint F z
  disjoint C z
  disjoint K z
  disjoint S z
  disjoint f s
  disjoint f x
  disjoint f z
  disjoint A f
  disjoint s x
  disjoint s z
  disjoint A s
  disjoint x z
  disjoint A x
  disjoint B x
  disjoint F f
  disjoint F s
  disjoint F x
  disjoint C x
  disjoint K f
  disjoint K s
  disjoint K x
  disjoint S f
  disjoint S s
  disjoint S x
  disjoint T f
  disjoint T s
  disjoint T x
  disjoint G x
  assert |- ( ph -> ( B ( S _D F ) C <-> ( B e. ( ( int ` T ) ` A ) /\ C e. ( G limCC B ) ) ) )

  proof
    wph
    cB
    cC
    cop
    #
    cS
    cF
    cdv
    co
    #
    wcel
    #
    @0
    vx
    cA
    cT
    cnt
    cfv
    cfv
    #
    vx
    cv
    #
    csn
    #
    vz
    cA
    @5
    cdif
    #
    vz
    cv
    #
    cF
    cfv
    #
    @4
    cF
    cfv
    #
    cmin
    co
    #
    @7
    @4
    cmin
    co
    #
    cdiv
    co
    #
    cmpt
    #
    @4
    climc
    co
    #
    cxp
    ciun
    #
    wcel
    cB
    cC
    @1
    wbr
    #
    cB
    @3
    wcel
    cC
    cG
    cB
    climc
    co
    #
    wcel
    wa
    wph
    @1
    @15
    @0
    wph
    @1
    @15
    wceq
    #
    @1
    @3
    cc
    cxp
    wss
    #
    wph
    cS
    cc
    wss
    cA
    cc
    cF
    wf
    cA
    cS
    wss
    @18
    @19
    wa
    eldv.s
    eldv.f
    eldv.a
    vx
    vz
    cA
    cS
    cT
    cF
    cK
    dvval.t
    dvval.k
    dvfval
    syl3anc
    simpld
    eleq2d
    @16
    @2
    cB
    cC
    @1
    df-br
    bicomi
    vx
    @3
    @14
    cB
    cC
    @17
    @4
    cB
    wceq
    #
    @13
    cG
    @4
    cB
    climc
    @20
    @13
    vz
    cA
    cB
    csn
    #
    cdif
    #
    @8
    cB
    cF
    cfv
    #
    cmin
    co
    #
    @7
    cB
    cmin
    co
    #
    cdiv
    co
    #
    cmpt
    cG
    @20
    vz
    @6
    @12
    @22
    @26
    @20
    @5
    @21
    cA
    @4
    cB
    sneq
    difeq2d
    @20
    @10
    @24
    @11
    @25
    cdiv
    @20
    @9
    @23
    @8
    cmin
    @4
    cB
    cF
    fveq2
    oveq2d
    @4
    cB
    @7
    cmin
    oveq2
    oveq12d
    mpteq12dv
    eldv.g
    syl6eqr
    @20
    id
    oveq12d
    opeliunxp2
    3bitr3g
end
