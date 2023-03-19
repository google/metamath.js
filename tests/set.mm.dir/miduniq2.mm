include "cfv.mm"
include "wceq.mm"
include "eqid.mm"
include "mirf.mm"
include "ffvelrnd.mm"
include "mircl.mm"
include "mirauto.mm"
include "mirmir.mm"
include "fveq2d.mm"
include "3eqtr3d.mm"
include "miduniq1.mm"
include "mirinv.mm"
include "mpbid.mm"
include "eqcomd.mm"

theorem miduniq2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cS: class S
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let cX: class X
  assume mirval.p: |- P = ( Base ` G )
  assume mirval.d: |- .- = ( dist ` G )
  assume mirval.i: |- I = ( Itv ` G )
  assume mirval.l: |- L = ( LineG ` G )
  assume mirval.s: |- S = ( pInvG ` G )
  assume mirval.g: |- ( ph -> G e. TarskiG )
  assume miduniq2.a: |- ( ph -> A e. P )
  assume miduniq2.b: |- ( ph -> B e. P )
  assume miduniq2.x: |- ( ph -> X e. P )
  assume miduniq2.e: |- ( ph -> ( ( S ` A ) ` ( ( S ` B ) ` X ) ) = ( ( S ` B ) ` ( ( S ` A ) ` X ) ) )


  assert |- ( ph -> A = B )

  proof
    wph
    cB
    cA
    wph
    cA
    cB
    cS
    cfv
    #
    cfv
    #
    cA
    wceq
    cB
    cA
    wceq
    wph
    @1
    cA
    cP
    cS
    cG
    cI
    cL
    c.mi
    cX
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    wph
    cP
    cP
    cA
    @0
    wph
    cB
    cP
    cS
    cG
    cI
    cL
    @0
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    miduniq2.b
    @0
    eqid
    #
    mirf
    #
    miduniq2.a
    ffvelrnd
    miduniq2.a
    miduniq2.x
    wph
    cX
    @0
    cfv
    #
    @0
    cfv
    #
    @1
    cS
    cfv
    #
    cfv
    cX
    cA
    cS
    cfv
    #
    cfv
    #
    @0
    cfv
    #
    @0
    cfv
    #
    cX
    @6
    cfv
    @8
    wph
    cA
    @4
    @9
    cP
    cS
    cB
    cG
    cI
    cL
    @0
    c.mi
    @1
    @5
    @10
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    @2
    @1
    eqid
    @5
    eqid
    @10
    eqid
    miduniq2.b
    miduniq2.a
    wph
    cP
    cP
    cX
    @0
    @3
    miduniq2.x
    ffvelrnd
    wph
    cP
    cP
    @8
    @0
    @3
    wph
    cA
    cP
    cS
    cG
    cI
    cL
    @7
    c.mi
    cX
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    miduniq2.a
    @7
    eqid
    miduniq2.x
    mircl
    #
    ffvelrnd
    miduniq2.e
    mirauto
    wph
    @5
    cX
    @6
    wph
    cB
    cX
    cP
    cS
    cG
    cI
    cL
    @0
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    miduniq2.b
    @2
    miduniq2.x
    mirmir
    fveq2d
    wph
    cB
    @8
    cP
    cS
    cG
    cI
    cL
    @0
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    miduniq2.b
    @2
    @11
    mirmir
    3eqtr3d
    miduniq1
    wph
    cB
    cA
    cP
    cS
    cG
    cI
    cL
    @0
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    miduniq2.b
    @2
    miduniq2.a
    mirinv
    mpbid
    eqcomd
end
