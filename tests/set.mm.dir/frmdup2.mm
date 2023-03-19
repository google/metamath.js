include "cfv.mm"
include "cs1.mm"
include "wcel.mm"
include "wceq.mm"
include "vrmdval.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "ccom.mm"
include "cgsu.mm"
include "co.mm"
include "cword.mm"
include "s1cld.mm"
include "cv.mm"
include "coeq2.mm"
include "oveq2d.mm"
include "ovex.mm"
include "fvmpt3i.mm"
include "syl.mm"
include "wf.mm"
include "s1co.mm"
include "ffvelrnd.mm"
include "gsumws1.mm"
include "3eqtrd.mm"
include "eqtrd.mm"

theorem frmdup2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cU: class U
  let cE: class E
  let cG: class G
  let cI: class I
  let cM: class M
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let vz: setvar z
  assume frmdup.m: |- M = ( freeMnd ` I )
  assume frmdup.b: |- B = ( Base ` G )
  assume frmdup.e: |- E = ( x e. Word I |-> ( G gsum ( A o. x ) ) )
  assume frmdup.g: |- ( ph -> G e. Mnd )
  assume frmdup.i: |- ( ph -> I e. X )
  assume frmdup.a: |- ( ph -> A : I --> B )
  assume frmdup2.u: |- U = ( varFMnd ` I )
  assume frmdup2.y: |- ( ph -> Y e. I )

  disjoint A x
  disjoint B x
  disjoint G x
  disjoint ph x
  disjoint Y x
  disjoint I x
  disjoint y z
  disjoint E y
  disjoint E z
  disjoint x y
  disjoint x z
  disjoint G y
  disjoint G z
  disjoint ph y
  disjoint ph z
  disjoint I y
  disjoint I z
  disjoint M y
  disjoint M z
  assert |- ( ph -> ( E ` ( U ` Y ) ) = ( A ` Y ) )

  proof
    wph
    cY
    cU
    cfv
    #
    cE
    cfv
    cY
    cs1
    #
    cE
    cfv
    #
    cY
    cA
    cfv
    #
    wph
    @0
    @1
    cE
    wph
    cI
    cX
    wcel
    cY
    cI
    wcel
    #
    @0
    @1
    wceq
    frmdup.i
    frmdup2.y
    cY
    cU
    cI
    cX
    frmdup2.u
    vrmdval
    syl2anc
    fveq2d
    wph
    @2
    cG
    cA
    @1
    ccom
    #
    cgsu
    co
    #
    cG
    @3
    cs1
    #
    cgsu
    co
    #
    @3
    wph
    @1
    cI
    cword
    #
    wcel
    @2
    @6
    wceq
    wph
    cY
    cI
    frmdup2.y
    s1cld
    vx
    @1
    cG
    cA
    vx
    cv
    #
    ccom
    #
    cgsu
    co
    @6
    @9
    cE
    @10
    @1
    wceq
    @11
    @5
    cG
    cgsu
    @10
    @1
    cA
    coeq2
    oveq2d
    frmdup.e
    cG
    @11
    cgsu
    ovex
    fvmpt3i
    syl
    wph
    @5
    @7
    cG
    cgsu
    wph
    @4
    cI
    cB
    cA
    wf
    @5
    @7
    wceq
    frmdup2.y
    frmdup.a
    cI
    cB
    cY
    cA
    s1co
    syl2anc
    oveq2d
    wph
    @3
    cB
    wcel
    @8
    @3
    wceq
    wph
    cI
    cB
    cY
    cA
    frmdup.a
    frmdup2.y
    ffvelrnd
    cB
    @3
    cG
    frmdup.b
    gsumws1
    syl
    3eqtrd
    eqtrd
end
