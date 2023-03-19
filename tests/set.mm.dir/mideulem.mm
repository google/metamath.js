include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "cfv.mm"
include "wrex.mm"
include "simprrl.mm"
include "cstrkg.mm"
include "ad2antrr.mm"
include "wne.mm"
include "cperpg.mm"
include "wbr.mm"
include "simplr.mm"
include "simprl.mm"
include "simprr.mm"
include "opphllem.mm"
include "reximddv.mm"
include "cleg.mm"
include "eqid.mm"
include "legov.mm"
include "mpbid.mm"
include "r19.29a.mm"

theorem mideulem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cT: class T
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let cO: class O
  let vm: setvar m
  let vr: setvar r
  let vs: setvar s
  let vy: setvar y
  let cR: class R
  assume colperpex.p: |- P = ( Base ` G )
  assume colperpex.d: |- .- = ( dist ` G )
  assume colperpex.i: |- I = ( Itv ` G )
  assume colperpex.l: |- L = ( LineG ` G )
  assume colperpex.g: |- ( ph -> G e. TarskiG )
  assume mideu.s: |- S = ( pInvG ` G )
  assume mideu.1: |- ( ph -> A e. P )
  assume mideu.2: |- ( ph -> B e. P )
  assume mideulem.1: |- ( ph -> A =/= B )
  assume mideulem.2: |- ( ph -> Q e. P )
  assume mideulem.3: |- ( ph -> O e. P )
  assume mideulem.4: |- ( ph -> T e. P )
  assume mideulem.5: |- ( ph -> ( A L B ) ( perpG ` G ) ( Q L B ) )
  assume mideulem.6: |- ( ph -> ( A L B ) ( perpG ` G ) ( A L O ) )
  assume mideulem.7: |- ( ph -> T e. ( A L B ) )
  assume mideulem.8: |- ( ph -> T e. ( Q I O ) )
  assume mideulem.9: |- ( ph -> ( A .- O ) ( leG ` G ) ( B .- Q ) )

  disjoint .- x
  disjoint A x
  disjoint B x
  disjoint I x
  disjoint O x
  disjoint P x
  disjoint Q x
  disjoint T x
  disjoint ph x
  disjoint .- m
  disjoint .- r
  disjoint .- s
  disjoint .- y
  disjoint m r
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint r s
  disjoint r x
  disjoint r y
  disjoint s x
  disjoint s y
  disjoint x y
  disjoint A m
  disjoint A r
  disjoint A s
  disjoint A y
  disjoint B m
  disjoint B r
  disjoint B s
  disjoint B y
  disjoint G r
  disjoint G y
  disjoint I m
  disjoint I r
  disjoint I s
  disjoint I y
  disjoint L m
  disjoint L s
  disjoint L y
  disjoint O m
  disjoint O r
  disjoint O s
  disjoint O y
  disjoint P m
  disjoint P r
  disjoint P s
  disjoint P y
  disjoint Q m
  disjoint Q r
  disjoint Q s
  disjoint Q y
  disjoint R m
  disjoint R s
  disjoint R x
  disjoint R y
  disjoint S m
  disjoint S r
  disjoint S s
  disjoint S y
  disjoint T m
  disjoint T s
  disjoint T y
  disjoint m ph
  disjoint ph r
  disjoint ph s
  disjoint ph y
  assert |- ( ph -> E. x e. P B = ( ( S ` x ) ` A ) )

  proof
    wph
    vr
    cv
    #
    cB
    cQ
    cI
    co
    wcel
    #
    cA
    cO
    c.mi
    co
    #
    cB
    @0
    c.mi
    co
    wceq
    #
    wa
    #
    cB
    cA
    vx
    cv
    #
    cS
    cfv
    #
    cfv
    wceq
    #
    vx
    cP
    wrex
    vr
    cP
    wph
    @0
    cP
    wcel
    #
    wa
    #
    @4
    wa
    #
    @7
    cO
    @0
    @6
    cfv
    wceq
    #
    wa
    @7
    vx
    cP
    @10
    @5
    cP
    wcel
    @7
    @11
    simprrl
    @10
    vx
    cA
    cB
    cP
    cQ
    @0
    cS
    cT
    cG
    cI
    cL
    c.mi
    cO
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    wph
    cG
    cstrkg
    wcel
    @8
    @4
    colperpex.g
    ad2antrr
    mideu.s
    wph
    cA
    cP
    wcel
    @8
    @4
    mideu.1
    ad2antrr
    wph
    cB
    cP
    wcel
    @8
    @4
    mideu.2
    ad2antrr
    wph
    cA
    cB
    wne
    @8
    @4
    mideulem.1
    ad2antrr
    wph
    cQ
    cP
    wcel
    @8
    @4
    mideulem.2
    ad2antrr
    wph
    cO
    cP
    wcel
    @8
    @4
    mideulem.3
    ad2antrr
    wph
    cT
    cP
    wcel
    @8
    @4
    mideulem.4
    ad2antrr
    wph
    cA
    cB
    cL
    co
    #
    cQ
    cB
    cL
    co
    cG
    cperpg
    cfv
    #
    wbr
    @8
    @4
    mideulem.5
    ad2antrr
    wph
    @12
    cA
    cO
    cL
    co
    @13
    wbr
    @8
    @4
    mideulem.6
    ad2antrr
    wph
    cT
    @12
    wcel
    @8
    @4
    mideulem.7
    ad2antrr
    wph
    cT
    cQ
    cO
    cI
    co
    wcel
    @8
    @4
    mideulem.8
    ad2antrr
    wph
    @8
    @4
    simplr
    @9
    @1
    @3
    simprl
    @9
    @1
    @3
    simprr
    opphllem
    reximddv
    wph
    @2
    cB
    cQ
    c.mi
    co
    cG
    cleg
    cfv
    #
    wbr
    @4
    vr
    cP
    wrex
    mideulem.9
    wph
    vr
    cA
    cO
    cB
    cQ
    cP
    cG
    cI
    @14
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    @14
    eqid
    colperpex.g
    mideu.1
    mideulem.3
    mideu.2
    mideulem.2
    legov
    mpbid
    r19.29a
end
