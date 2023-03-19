include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "crio.mm"
include "cmpt.mm"
include "cvv.mm"
include "cmir.mm"
include "cfv.mm"
include "cbs.mm"
include "cds.mm"
include "citv.mm"
include "df-mir.mm"
include "a1i.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveqd.mm"
include "eqeq12d.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "riotaeqbidv.mm"
include "mpteq12dv.mm"
include "adantl.mm"
include "cstrkg.mm"
include "elex.mm"
include "syl.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmptd.mm"
include "syl5eq.mm"
include "simpll.mm"
include "oveq1d.mm"
include "eleq1d.mm"
include "riotabidva.mm"
include "mpteq2dva.mm"

theorem mirval
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cP: class P
  let cS: class S
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let vx: setvar x
  let cB: class B
  let cC: class C
  let vg: setvar g
  let cM: class M
  assume mirval.p: |- P = ( Base ` G )
  assume mirval.d: |- .- = ( dist ` G )
  assume mirval.i: |- I = ( Itv ` G )
  assume mirval.l: |- L = ( LineG ` G )
  assume mirval.s: |- S = ( pInvG ` G )
  assume mirval.g: |- ( ph -> G e. TarskiG )
  assume mirval.a: |- ( ph -> A e. P )

  disjoint y z
  disjoint A y
  disjoint A z
  disjoint G y
  disjoint G z
  disjoint I y
  disjoint I z
  disjoint P y
  disjoint P z
  disjoint ph y
  disjoint ph z
  disjoint .- y
  disjoint .- z
  disjoint x y
  disjoint x z
  disjoint A x
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
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint I g
  disjoint I x
  disjoint P g
  disjoint P x
  disjoint g ph
  disjoint ph x
  disjoint .- g
  disjoint .- x
  assert |- ( ph -> ( S ` A ) = ( y e. P |-> ( iota_ z e. P ( ( A .- z ) = ( A .- y ) /\ A e. ( z I y ) ) ) ) )

  proof
    wph
    vx
    cA
    vy
    cP
    vx
    cv
    #
    vz
    cv
    #
    c.mi
    co
    #
    @0
    vy
    cv
    #
    c.mi
    co
    #
    wceq
    #
    @0
    @1
    @3
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
    cmpt
    #
    vy
    cP
    cA
    @1
    c.mi
    co
    #
    cA
    @3
    c.mi
    co
    #
    wceq
    #
    cA
    @6
    wcel
    #
    wa
    #
    vz
    cP
    crio
    #
    cmpt
    #
    cP
    cS
    cvv
    wph
    cS
    cG
    cmir
    cfv
    vx
    cP
    @10
    cmpt
    #
    mirval.s
    wph
    vg
    cG
    vx
    vg
    cv
    #
    cbs
    cfv
    #
    vy
    @20
    @0
    @1
    @19
    cds
    cfv
    #
    co
    #
    @0
    @3
    @21
    co
    #
    wceq
    #
    @0
    @1
    @3
    @19
    citv
    cfv
    #
    co
    #
    wcel
    #
    wa
    #
    vz
    @20
    crio
    #
    cmpt
    #
    cmpt
    #
    @18
    cvv
    cmir
    cvv
    cmir
    vg
    cvv
    @31
    cmpt
    wceq
    wph
    vg
    vx
    vy
    vz
    df-mir
    a1i
    @19
    cG
    wceq
    #
    @31
    @18
    wceq
    wph
    @32
    vx
    @20
    @30
    cP
    @10
    @32
    @20
    cG
    cbs
    cfv
    #
    cP
    @19
    cG
    cbs
    fveq2
    mirval.p
    syl6eqr
    #
    @32
    vy
    @20
    @29
    cP
    @9
    @34
    @32
    @28
    @8
    vz
    @20
    cP
    @34
    @32
    @24
    @5
    @27
    @7
    @32
    @22
    @2
    @23
    @4
    @32
    @21
    c.mi
    @0
    @1
    @32
    @21
    cG
    cds
    cfv
    c.mi
    @19
    cG
    cds
    fveq2
    mirval.d
    syl6eqr
    #
    oveqd
    @32
    @21
    c.mi
    @0
    @3
    @35
    oveqd
    eqeq12d
    @32
    @26
    @6
    @0
    @32
    @25
    cI
    @1
    @3
    @32
    @25
    cG
    citv
    cfv
    cI
    @19
    cG
    citv
    fveq2
    mirval.i
    syl6eqr
    oveqd
    eleq2d
    anbi12d
    riotaeqbidv
    mpteq12dv
    mpteq12dv
    adantl
    wph
    cG
    cstrkg
    wcel
    cG
    cvv
    wcel
    mirval.g
    cG
    cstrkg
    elex
    syl
    @18
    cvv
    wcel
    wph
    vx
    cP
    @10
    cP
    @33
    cvv
    mirval.p
    cG
    cbs
    fvex
    eqeltri
    #
    mptex
    a1i
    fvmptd
    syl5eq
    @0
    cA
    wceq
    #
    @10
    @17
    wceq
    wph
    @37
    vy
    cP
    @9
    @16
    @37
    @3
    cP
    wcel
    #
    wa
    #
    @8
    @15
    vz
    cP
    @39
    @1
    cP
    wcel
    #
    wa
    #
    @5
    @13
    @7
    @14
    @41
    @2
    @11
    @4
    @12
    @41
    @0
    cA
    @1
    c.mi
    @37
    @38
    @40
    simpll
    #
    oveq1d
    @41
    @0
    cA
    @3
    c.mi
    @42
    oveq1d
    eqeq12d
    @41
    @0
    cA
    @6
    @42
    eleq1d
    anbi12d
    riotabidva
    mpteq2dva
    adantl
    mirval.a
    @17
    cvv
    wcel
    wph
    vy
    cP
    @16
    @36
    mptex
    a1i
    fvmptd
end
