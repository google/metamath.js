include "cfv.mm"
include "eqid.mm"
include "mircl.mm"
include "eqidd.mm"
include "eqcomd.mm"
include "miduniq.mm"

theorem miduniq1
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
  assume miduniq1.a: |- ( ph -> A e. P )
  assume miduniq1.b: |- ( ph -> B e. P )
  assume miduniq1.x: |- ( ph -> X e. P )
  assume miduniq1.e: |- ( ph -> ( ( S ` A ) ` X ) = ( ( S ` B ) ` X ) )


  assert |- ( ph -> A = B )

  proof
    wph
    cA
    cB
    cP
    cS
    cG
    cI
    cL
    c.mi
    cX
    cX
    cA
    cS
    cfv
    #
    cfv
    #
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    miduniq1.a
    miduniq1.b
    miduniq1.x
    wph
    cA
    cP
    cS
    cG
    cI
    cL
    @0
    c.mi
    cX
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    miduniq1.a
    @0
    eqid
    miduniq1.x
    mircl
    wph
    @1
    eqidd
    wph
    @1
    cX
    cB
    cS
    cfv
    cfv
    miduniq1.e
    eqcomd
    miduniq
end
