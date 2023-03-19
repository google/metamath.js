include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "cds.mm"
include "cfv.mm"
include "eqid.mm"
include "cstrkg.mm"
include "ad3antrrr.mm"
include "crn.mm"
include "simplr.mm"
include "tglnpt.mm"
include "simpr.mm"
include "simpllr.mm"
include "oveq2d.mm"
include "eleqtrrd.mm"
include "axtgbtwnid.mm"
include "eqeltrd.mm"
include "wrex.mm"
include "wn.mm"
include "wbr.mm"
include "islnopp.mm"
include "mpbid.mm"
include "simprd.mm"
include "adantr.mm"
include "r19.29a.mm"
include "oppne1.mm"
include "pm2.65da.mm"
include "neqned.mm"

theorem oppne3
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
  assert |- ( ph -> A =/= B )

  proof
    wph
    cA
    cB
    wph
    cA
    cB
    wceq
    #
    cA
    cD
    wcel
    #
    wph
    @0
    wa
    #
    vt
    cv
    #
    cA
    cB
    cI
    co
    #
    wcel
    #
    @1
    vt
    cD
    @2
    @3
    cD
    wcel
    #
    wa
    #
    @5
    wa
    #
    cA
    @3
    cD
    @8
    cP
    cG
    cI
    cG
    cds
    cfv
    #
    cA
    @3
    hpg.p
    @9
    eqid
    hpg.i
    wph
    cG
    cstrkg
    wcel
    @0
    @6
    @5
    opphl.g
    ad3antrrr
    #
    wph
    cA
    cP
    wcel
    @0
    @6
    @5
    oppcom.a
    ad3antrrr
    @8
    cD
    cP
    cG
    cI
    cL
    @3
    hpg.p
    opphl.l
    hpg.i
    @10
    wph
    cD
    cL
    crn
    wcel
    @0
    @6
    @5
    opphl.d
    ad3antrrr
    @2
    @6
    @5
    simplr
    #
    tglnpt
    @8
    @3
    @4
    cA
    cA
    cI
    co
    @7
    @5
    simpr
    @8
    cA
    cB
    cA
    cI
    wph
    @0
    @6
    @5
    simpllr
    oveq2d
    eleqtrrd
    axtgbtwnid
    @11
    eqeltrd
    wph
    @5
    vt
    cD
    wrex
    #
    @0
    wph
    @1
    wn
    #
    cB
    cD
    wcel
    wn
    wa
    #
    @12
    wph
    cA
    cB
    cO
    wbr
    @14
    @12
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
    simprd
    adantr
    r19.29a
    wph
    @13
    @0
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
    adantr
    pm2.65da
    neqned
end
