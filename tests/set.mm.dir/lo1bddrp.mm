include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "crp.mm"
include "lo1bdd2.mm"
include "wcel.mm"
include "wa.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "simpr.mm"
include "recnd.mm"
include "abscld.mm"
include "absge0d.mm"
include "ge0p1rpd.mm"
include "simplr.mm"
include "adantr.mm"
include "peano2re.mm"
include "syl.mm"
include "leabsd.mm"
include "lep1d.mm"
include "letrd.mm"
include "wi.mm"
include "adantlr.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "ralimdva.mm"
include "wceq.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem lo1bddrp
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vm: setvar m
  let cM: class M
  let vn: setvar n
  assume lo1bdd2.1: |- ( ph -> A C_ RR )
  assume lo1bdd2.2: |- ( ph -> C e. RR )
  assume lo1bdd2.3: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume lo1bdd2.4: |- ( ph -> ( x e. A |-> B ) e. <_O(1) )
  assume lo1bdd2.5: |- ( ( ph /\ ( y e. RR /\ C <_ y ) ) -> M e. RR )
  assume lo1bdd2.6: |- ( ( ( ph /\ x e. A ) /\ ( ( y e. RR /\ C <_ y ) /\ x < y ) ) -> B <_ M )

  disjoint m x
  disjoint m y
  disjoint A m
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B m
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint ph x
  disjoint ph y
  disjoint M m
  disjoint M x
  disjoint m n
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint B n
  disjoint C n
  disjoint n ph
  disjoint M n
  assert |- ( ph -> E. m e. RR+ A. x e. A B <_ m )

  proof
    wph
    cB
    vn
    cv
    #
    cle
    wbr
    #
    vx
    cA
    wral
    #
    vn
    cr
    wrex
    cB
    vm
    cv
    #
    cle
    wbr
    #
    vx
    cA
    wral
    #
    vm
    crp
    wrex
    #
    wph
    vx
    vy
    cA
    cB
    cC
    vn
    cM
    lo1bdd2.1
    lo1bdd2.2
    lo1bdd2.3
    lo1bdd2.4
    lo1bdd2.5
    lo1bdd2.6
    lo1bdd2
    wph
    @2
    @6
    vn
    cr
    wph
    @0
    cr
    wcel
    #
    wa
    #
    @0
    cabs
    cfv
    #
    c1
    caddc
    co
    #
    crp
    wcel
    @2
    cB
    @10
    cle
    wbr
    #
    vx
    cA
    wral
    #
    @6
    @8
    @9
    @8
    @0
    @8
    @0
    wph
    @7
    simpr
    recnd
    #
    abscld
    #
    @8
    @0
    @13
    absge0d
    ge0p1rpd
    @8
    @1
    @11
    vx
    cA
    @8
    vx
    cv
    cA
    wcel
    #
    wa
    #
    @1
    @0
    @10
    cle
    wbr
    #
    @11
    @16
    @0
    @9
    @10
    wph
    @7
    @15
    simplr
    #
    @8
    @9
    cr
    wcel
    #
    @15
    @14
    adantr
    #
    @16
    @19
    @10
    cr
    wcel
    #
    @20
    @9
    peano2re
    syl
    #
    @16
    @0
    @18
    leabsd
    @16
    @9
    @20
    lep1d
    letrd
    @16
    cB
    cr
    wcel
    #
    @7
    @21
    @1
    @17
    wa
    @11
    wi
    wph
    @15
    @23
    @7
    lo1bdd2.3
    adantlr
    @18
    @22
    cB
    @0
    @10
    letr
    syl3anc
    mpan2d
    ralimdva
    @5
    @12
    vm
    @10
    crp
    @3
    @10
    wceq
    @4
    @11
    vx
    cA
    @3
    @10
    cB
    cle
    breq2
    ralbidv
    rspcev
    syl6an
    rexlimdva
    mpd
end
