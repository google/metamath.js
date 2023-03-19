include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "crio.mm"
include "cvv.mm"
include "cfv.mm"
include "cmpt.mm"
include "mirval.mm"
include "syl5eq.mm"
include "simplr.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "riotabidva.mm"
include "riotaex.mm"
include "a1i.mm"
include "fvmptd.mm"

theorem mirfv
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cP: class P
  let cS: class S
  let cG: class G
  let cI: class I
  let cL: class L
  let cM: class M
  let c.mi: class .-
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
  assume mirfv.b: |- ( ph -> B e. P )

  disjoint A z
  disjoint B z
  disjoint G z
  disjoint M z
  disjoint I z
  disjoint P z
  disjoint ph z
  disjoint .- z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint G g
  disjoint G x
  disjoint G y
  disjoint M x
  disjoint M y
  disjoint I g
  disjoint I x
  disjoint I y
  disjoint P g
  disjoint P x
  disjoint P y
  disjoint g ph
  disjoint ph x
  disjoint ph y
  disjoint .- g
  disjoint .- x
  disjoint .- y
  assert |- ( ph -> ( M ` B ) = ( iota_ z e. P ( ( A .- z ) = ( A .- B ) /\ A e. ( z I B ) ) ) )

  proof
    wph
    vy
    cB
    cA
    vz
    cv
    #
    c.mi
    co
    #
    cA
    vy
    cv
    #
    c.mi
    co
    #
    wceq
    #
    cA
    @0
    @2
    cI
    co
    #
    wcel
    #
    wa
    #
    vz
    cP
    crio
    #
    @1
    cA
    cB
    c.mi
    co
    #
    wceq
    #
    cA
    @0
    cB
    cI
    co
    #
    wcel
    #
    wa
    #
    vz
    cP
    crio
    #
    cP
    cM
    cvv
    wph
    cM
    cA
    cS
    cfv
    vy
    cP
    @8
    cmpt
    mirfv.m
    wph
    vy
    vz
    cA
    cP
    cS
    cG
    cI
    cL
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    mirval.a
    mirval
    syl5eq
    wph
    @2
    cB
    wceq
    #
    wa
    #
    @7
    @13
    vz
    cP
    @16
    @0
    cP
    wcel
    #
    wa
    #
    @4
    @10
    @6
    @12
    @18
    @3
    @9
    @1
    @18
    @2
    cB
    cA
    c.mi
    wph
    @15
    @17
    simplr
    #
    oveq2d
    eqeq2d
    @18
    @5
    @11
    cA
    @18
    @2
    cB
    @0
    cI
    @19
    oveq2d
    eleq2d
    anbi12d
    riotabidva
    mirfv.b
    @14
    cvv
    wcel
    wph
    @13
    vz
    cP
    riotaex
    a1i
    fvmptd
end
