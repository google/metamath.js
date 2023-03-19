include "wbr.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "cstrkg.mm"
include "ad3antrrr.mm"
include "crn.mm"
include "simplr.mm"
include "tglnpt.mm"
include "simpr.mm"
include "axtgbtwnid.mm"
include "eqeltrd.mm"
include "wn.mm"
include "wrex.mm"
include "islnopp.mm"
include "simplbda.mm"
include "r19.29a.mm"
include "simprbda.mm"
include "simpld.mm"
include "pm2.65da.mm"

theorem oppnid
  let wph: wff ph
  let vt: setvar t
  let cA: class A
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
  let cB: class B
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
  assume oppnid.1: |- ( ph -> A e. P )

  disjoint D a
  disjoint D b
  disjoint a b
  disjoint I a
  disjoint I b
  disjoint P a
  disjoint P b
  disjoint A t
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
  disjoint B t
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
  assert |- ( ph -> -. A O A )

  proof
    wph
    cA
    cA
    cO
    wbr
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
    cA
    cI
    co
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
    @4
    wa
    #
    cA
    @3
    cD
    @7
    cP
    cG
    cI
    c.mi
    cA
    @3
    hpg.p
    hpg.d
    hpg.i
    wph
    cG
    cstrkg
    wcel
    @0
    @5
    @4
    opphl.g
    ad3antrrr
    #
    wph
    cA
    cP
    wcel
    @0
    @5
    @4
    oppnid.1
    ad3antrrr
    @7
    cD
    cP
    cG
    cI
    cL
    @3
    hpg.p
    opphl.l
    hpg.i
    @8
    wph
    cD
    cL
    crn
    wcel
    @0
    @5
    @4
    opphl.d
    ad3antrrr
    @2
    @5
    @4
    simplr
    #
    tglnpt
    @6
    @4
    simpr
    axtgbtwnid
    @9
    eqeltrd
    wph
    @0
    @1
    wn
    #
    @10
    wa
    #
    @4
    vt
    cD
    wrex
    #
    wph
    vt
    cA
    cA
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
    oppnid.1
    oppnid.1
    islnopp
    #
    simplbda
    r19.29a
    @2
    @10
    @10
    wph
    @0
    @11
    @12
    @13
    simprbda
    simpld
    pm2.65da
end
