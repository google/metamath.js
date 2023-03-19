include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "cuz.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "a1i.mm"
include "wa.mm"
include "recnd.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "climsub.mm"
include "cr.mm"
include "resubcld.mm"
include "eqeltrd.mm"
include "subge0d.mm"
include "mpbird.mm"
include "breqtrrd.mm"
include "climge0.mm"
include "climrecl.mm"
include "mpbid.mm"

theorem climle
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let vj: setvar j
  let cH: class H
  assume climadd.1: |- Z = ( ZZ>= ` M )
  assume climadd.2: |- ( ph -> M e. ZZ )
  assume climadd.4: |- ( ph -> F ~~> A )
  assume climle.5: |- ( ph -> G ~~> B )
  assume climle.6: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. RR )
  assume climle.7: |- ( ( ph /\ k e. Z ) -> ( G ` k ) e. RR )
  assume climle.8: |- ( ( ph /\ k e. Z ) -> ( F ` k ) <_ ( G ` k ) )

  disjoint B k
  disjoint F k
  disjoint k ph
  disjoint A k
  disjoint G k
  disjoint M k
  disjoint Z k
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint B v
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C k
  disjoint j k
  disjoint j u
  disjoint j v
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint F u
  disjoint F v
  disjoint F y
  disjoint F z
  disjoint j x
  disjoint j ph
  disjoint ph u
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint A j
  disjoint A u
  disjoint A v
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint G j
  disjoint G v
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint H k
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint M j
  disjoint M x
  disjoint Z j
  disjoint Z x
  disjoint Z y
  disjoint Z z
  assert |- ( ph -> A <_ B )

  proof
    wph
    cc0
    cB
    cA
    cmin
    co
    #
    cle
    wbr
    cA
    cB
    cle
    wbr
    wph
    @0
    vk
    vj
    cZ
    vj
    cv
    #
    cG
    cfv
    #
    @1
    cF
    cfv
    #
    cmin
    co
    #
    cmpt
    #
    cM
    cZ
    climadd.1
    climadd.2
    wph
    cB
    cA
    vk
    cG
    cF
    @5
    cM
    cvv
    cZ
    climadd.1
    climadd.2
    climle.5
    @5
    cvv
    wcel
    wph
    vj
    cZ
    @4
    cZ
    cM
    cuz
    cfv
    cvv
    climadd.1
    cM
    cuz
    fvex
    eqeltri
    mptex
    a1i
    climadd.4
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @6
    cG
    cfv
    #
    climle.7
    recnd
    @8
    @6
    cF
    cfv
    #
    climle.6
    recnd
    @7
    @6
    @5
    cfv
    #
    @9
    @10
    cmin
    co
    #
    wceq
    wph
    vj
    @6
    @4
    @12
    cZ
    @5
    @1
    @6
    wceq
    @2
    @9
    @3
    @10
    cmin
    @1
    @6
    cG
    fveq2
    @1
    @6
    cF
    fveq2
    oveq12d
    @5
    eqid
    @9
    @10
    cmin
    ovex
    fvmpt
    adantl
    #
    climsub
    @8
    @11
    @12
    cr
    @13
    @8
    @9
    @10
    climle.7
    climle.6
    resubcld
    eqeltrd
    @8
    cc0
    @12
    @11
    cle
    @8
    cc0
    @12
    cle
    wbr
    @10
    @9
    cle
    wbr
    climle.8
    @8
    @9
    @10
    climle.7
    climle.6
    subge0d
    mpbird
    @13
    breqtrrd
    climge0
    wph
    cB
    cA
    wph
    cB
    vk
    cG
    cM
    cZ
    climadd.1
    climadd.2
    climle.5
    climle.7
    climrecl
    wph
    cA
    vk
    cF
    cM
    cZ
    climadd.1
    climadd.2
    climadd.4
    climle.6
    climrecl
    subge0d
    mpbid
end
