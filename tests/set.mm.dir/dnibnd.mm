include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cfl.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "cabs.mm"
include "wa.mm"
include "cr.mm"
include "wcel.mm"
include "adantr.mm"
include "simpr.mm"
include "dnibndlem13.mm"
include "wceq.mm"
include "dnicld2.mm"
include "recnd.mm"
include "abssubd.mm"
include "breqtrd.mm"
include "eqbrtrd.mm"
include "halfre.mm"
include "a1i.mm"
include "readdcld.mm"
include "reflcl.mm"
include "syl.mm"
include "letrid.mm"
include "mpjaodan.mm"

theorem dnibnd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cT: class T
  assume dnibnd.1: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume dnibnd.2: |- ( ph -> A e. RR )
  assume dnibnd.3: |- ( ph -> B e. RR )

  disjoint A x
  disjoint B x
  assert |- ( ph -> ( abs ` ( ( T ` B ) - ( T ` A ) ) ) <_ ( abs ` ( B - A ) ) )

  proof
    wph
    cA
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    #
    cfl
    cfv
    #
    cB
    @0
    caddc
    co
    #
    cfl
    cfv
    #
    cle
    wbr
    #
    cB
    cT
    cfv
    #
    cA
    cT
    cfv
    #
    cmin
    co
    cabs
    cfv
    #
    cB
    cA
    cmin
    co
    cabs
    cfv
    #
    cle
    wbr
    @4
    @2
    cle
    wbr
    #
    wph
    @5
    wa
    vx
    cA
    cB
    cT
    dnibnd.1
    wph
    cA
    cr
    wcel
    #
    @5
    dnibnd.2
    adantr
    wph
    cB
    cr
    wcel
    #
    @5
    dnibnd.3
    adantr
    wph
    @5
    simpr
    dnibndlem13
    wph
    @10
    wa
    #
    @8
    @7
    @6
    cmin
    co
    cabs
    cfv
    #
    @9
    cle
    wph
    @8
    @14
    wceq
    @10
    wph
    @6
    @7
    wph
    @6
    wph
    vx
    cB
    cT
    dnibnd.1
    dnibnd.3
    dnicld2
    recnd
    wph
    @7
    wph
    vx
    cA
    cT
    dnibnd.1
    dnibnd.2
    dnicld2
    recnd
    abssubd
    adantr
    @13
    @14
    cA
    cB
    cmin
    co
    cabs
    cfv
    #
    @9
    cle
    @13
    vx
    cB
    cA
    cT
    dnibnd.1
    wph
    @12
    @10
    dnibnd.3
    adantr
    wph
    @11
    @10
    dnibnd.2
    adantr
    wph
    @10
    simpr
    dnibndlem13
    wph
    @15
    @9
    wceq
    @10
    wph
    cA
    cB
    wph
    cA
    dnibnd.2
    recnd
    wph
    cB
    dnibnd.3
    recnd
    abssubd
    adantr
    breqtrd
    eqbrtrd
    wph
    @2
    @4
    wph
    @1
    cr
    wcel
    @2
    cr
    wcel
    wph
    cA
    @0
    dnibnd.2
    @0
    cr
    wcel
    wph
    halfre
    a1i
    #
    readdcld
    @1
    reflcl
    syl
    wph
    @3
    cr
    wcel
    @4
    cr
    wcel
    wph
    cB
    @0
    dnibnd.3
    @16
    readdcld
    @3
    reflcl
    syl
    letrid
    mpjaodan
end
