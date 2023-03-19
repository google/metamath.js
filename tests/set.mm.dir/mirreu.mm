include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "mircl.mm"
include "mirmir.mm"
include "wa.mm"
include "cstrkg.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simpr.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "ex.mm"
include "ralrimiva.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "eqreu.mm"
include "syl3anc.mm"

theorem mirreu
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cS: class S
  let cG: class G
  let cI: class I
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let va: setvar a
  let vz: setvar z
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let vg: setvar g
  assume mirval.p: |- P = ( Base ` G )
  assume mirval.d: |- .- = ( dist ` G )
  assume mirval.i: |- I = ( Itv ` G )
  assume mirval.l: |- L = ( LineG ` G )
  assume mirval.s: |- S = ( pInvG ` G )
  assume mirval.g: |- ( ph -> G e. TarskiG )
  assume mirval.a: |- ( ph -> A e. P )
  assume mirfv.m: |- M = ( S ` A )
  assume mirmir.b: |- ( ph -> B e. P )

  disjoint B a
  disjoint M a
  disjoint P a
  disjoint a ph
  disjoint a z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint G g
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint I g
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint P g
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint g ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint .- g
  disjoint .- x
  disjoint .- y
  disjoint .- z
  disjoint B x
  assert |- ( ph -> E! a e. P ( M ` a ) = B )

  proof
    wph
    cB
    cM
    cfv
    #
    cP
    wcel
    @0
    cM
    cfv
    #
    cB
    wceq
    #
    va
    cv
    #
    cM
    cfv
    #
    cB
    wceq
    #
    @3
    @0
    wceq
    #
    wi
    #
    va
    cP
    wral
    @5
    va
    cP
    wreu
    wph
    cA
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    cB
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    mirval.a
    mirfv.m
    mirmir.b
    mircl
    wph
    cA
    cB
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    mirval.a
    mirfv.m
    mirmir.b
    mirmir
    wph
    @7
    va
    cP
    wph
    @3
    cP
    wcel
    #
    wa
    #
    @5
    @6
    @9
    @5
    wa
    #
    @4
    cM
    cfv
    @3
    @0
    @10
    cA
    @3
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    wph
    cG
    cstrkg
    wcel
    @8
    @5
    mirval.g
    ad2antrr
    wph
    cA
    cP
    wcel
    @8
    @5
    mirval.a
    ad2antrr
    mirfv.m
    wph
    @8
    @5
    simplr
    mirmir
    @10
    @4
    cB
    cM
    @9
    @5
    simpr
    fveq2d
    eqtr3d
    ex
    ralrimiva
    @5
    @2
    va
    cP
    @0
    @6
    @4
    @1
    cB
    @3
    @0
    cM
    fveq2
    eqeq1d
    eqreu
    syl3anc
end
