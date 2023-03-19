include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wne.mm"
include "wa.mm"
include "c2.mm"
include "cstrkgld.mm"
include "wbr.mm"
include "wcel.mm"
include "cstrkg.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "simplr.mm"
include "wn.mm"
include "wo.mm"
include "oppne1.mm"
include "simprl.mm"
include "neleqtrd.mm"
include "simprr.mm"
include "neneqd.mm"
include "jca.mm"
include "ioran.mm"
include "sylibr.mm"
include "ncoltgdim2.mm"
include "tgisline.mm"
include "r19.29vva.mm"

theorem opptgdim2
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
  let vx: setvar x
  let vy: setvar y
  let vm: setvar m
  let vp: setvar p
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
  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint D x
  disjoint D y
  disjoint G x
  disjoint G y
  disjoint I x
  disjoint I y
  disjoint P x
  disjoint P y
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
  assert |- ( ph -> G TarskiGDim>= 2 )

  proof
    wph
    cD
    vx
    cv
    #
    vy
    cv
    #
    cL
    co
    #
    wceq
    #
    @0
    @1
    wne
    #
    wa
    #
    cG
    c2
    cstrkgld
    wbr
    vx
    vy
    cP
    cP
    wph
    @0
    cP
    wcel
    #
    wa
    #
    @1
    cP
    wcel
    #
    wa
    #
    @5
    wa
    #
    cP
    cG
    cI
    cL
    @0
    @1
    cA
    hpg.p
    opphl.l
    hpg.i
    wph
    cG
    cstrkg
    wcel
    @6
    @8
    @5
    opphl.g
    ad3antrrr
    wph
    @6
    @8
    @5
    simpllr
    @7
    @8
    @5
    simplr
    wph
    cA
    cP
    wcel
    @6
    @8
    @5
    oppcom.a
    ad3antrrr
    @10
    cA
    @2
    wcel
    #
    wn
    #
    @0
    @1
    wceq
    #
    wn
    #
    wa
    @11
    @13
    wo
    wn
    @10
    @12
    @14
    @10
    cD
    @2
    cA
    wph
    cA
    cD
    wcel
    wn
    @6
    @8
    @5
    wph
    vt
    cA
    cB
    cD
    cP
    cG
    cI
    cL
    c.mi
    cO
    va
    vb
    hpg.p
    hpg.d
    hpg.i
    hpg.o
    opphl.l
    opphl.d
    opphl.g
    oppcom.a
    oppcom.b
    oppcom.o
    oppne1
    ad3antrrr
    @9
    @3
    @4
    simprl
    neleqtrd
    @10
    @0
    @1
    @9
    @3
    @4
    simprr
    neneqd
    jca
    @11
    @13
    ioran
    sylibr
    ncoltgdim2
    wph
    vx
    vy
    cD
    cP
    cG
    cI
    cL
    hpg.p
    hpg.i
    opphl.l
    opphl.g
    opphl.d
    tgisline
    r19.29vva
end
