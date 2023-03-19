include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wrex.mm"
include "wbr.mm"
include "islnopp.mm"
include "mpbid.mm"
include "simpld.mm"
include "simprd.mm"

theorem oppne2
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let cO: class O
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vp: setvar p
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cR: class R
  let cC: class C
  let cU: class U
  let cK: class K
  let cM: class M
  let cN: class N
  let cS: class S
  let cV: class V
  assume hpg.p: |- P = ( Base ` G )
  assume hpg.d: |- .- = ( dist ` G )
  assume hpg.i: |- I = ( Itv ` G )
  assume hpg.o: |- O = { <. a , b >. | ( ( a e. ( P \ D ) /\ b e. ( P \ D ) ) /\ E. t e. D t e. ( a I b ) ) }
  assume opphl.l: |- L = ( LineG ` G )
  assume opphl.d: |- ( ph -> D e. ran L )
  assume opphl.g: |- ( ph -> G e. TarskiG )
  assume oppcom.a: |- ( ph -> A e. P )
  assume oppcom.b: |- ( ph -> B e. P )
  assume oppcom.o: |- ( ph -> A O B )

  disjoint D a
  disjoint D b
  disjoint a b
  disjoint I a
  disjoint I b
  disjoint P a
  disjoint P b
  disjoint A t
  disjoint B t
  disjoint D t
  disjoint G t
  disjoint L t
  disjoint I t
  disjoint O t
  disjoint P t
  disjoint ph t
  disjoint .- t
  disjoint a t
  disjoint b t
  disjoint A m
  disjoint A p
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint m p
  disjoint m t
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint p t
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B m
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint D m
  disjoint D p
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint R m
  disjoint R p
  disjoint R t
  disjoint C m
  disjoint C p
  disjoint C t
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint G m
  disjoint G p
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint L m
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint U m
  disjoint U p
  disjoint U t
  disjoint I m
  disjoint I p
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint K p
  disjoint K t
  disjoint M t
  disjoint O m
  disjoint O x
  disjoint O y
  disjoint O z
  disjoint N m
  disjoint N p
  disjoint N t
  disjoint P m
  disjoint P p
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint S m
  disjoint S p
  disjoint S t
  disjoint V m
  disjoint V t
  disjoint m ph
  disjoint p ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint .- m
  disjoint .- p
  disjoint .- x
  disjoint .- y
  disjoint .- z
  assert |- ( ph -> -. B e. D )

  proof
    wph
    cA
    cD
    wcel
    wn
    #
    cB
    cD
    wcel
    wn
    #
    wph
    @0
    @1
    wa
    #
    vt
    cv
    cA
    cB
    cI
    co
    wcel
    vt
    cD
    wrex
    #
    wph
    cA
    cB
    cO
    wbr
    @2
    @3
    wa
    oppcom.o
    wph
    vt
    cA
    cB
    cD
    cP
    cG
    cI
    c.mi
    cO
    va
    vb
    hpg.p
    hpg.d
    hpg.i
    hpg.o
    oppcom.a
    oppcom.b
    islnopp
    mpbid
    simpld
    simprd
end
