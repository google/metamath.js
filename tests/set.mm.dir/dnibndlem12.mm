include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "caddc.mm"
include "cfl.mm"
include "dnicld1.mm"
include "resubcld.mm"
include "recnd.mm"
include "abscld.mm"
include "1red.mm"
include "rehalfcld.mm"
include "dnibndlem11.mm"
include "clt.mm"
include "halflt1.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "halfre.mm"
include "1re.mm"
include "pm3.2i.mm"
include "ltle.mm"
include "ax-mp.mm"
include "a1i.mm"
include "letrd.mm"
include "dnibndlem10.mm"
include "leabsd.mm"
include "dnibndlem1.mm"
include "mpbird.mm"

theorem dnibndlem12
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cT: class T
  assume dnibndlem12.1: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume dnibndlem12.2: |- ( ph -> A e. RR )
  assume dnibndlem12.3: |- ( ph -> B e. RR )
  assume dnibndlem12.4: |- ( ph -> ( ( |_ ` ( A + ( 1 / 2 ) ) ) + 2 ) <_ ( |_ ` ( B + ( 1 / 2 ) ) ) )

  disjoint A x
  disjoint B x
  assert |- ( ph -> ( abs ` ( ( T ` B ) - ( T ` A ) ) ) <_ ( abs ` ( B - A ) ) )

  proof
    wph
    cB
    cT
    cfv
    cA
    cT
    cfv
    cmin
    co
    cabs
    cfv
    cB
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    cle
    wbr
    cB
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    cfl
    cfv
    cB
    cmin
    co
    cabs
    cfv
    #
    cA
    @2
    caddc
    co
    cfl
    cfv
    cA
    cmin
    co
    cabs
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @1
    cle
    wbr
    wph
    @6
    c1
    @1
    wph
    @5
    wph
    @5
    wph
    @3
    @4
    wph
    cB
    dnibndlem12.3
    dnicld1
    wph
    cA
    dnibndlem12.2
    dnicld1
    resubcld
    recnd
    abscld
    #
    wph
    1red
    #
    wph
    @0
    wph
    @0
    wph
    cB
    cA
    dnibndlem12.3
    dnibndlem12.2
    resubcld
    #
    recnd
    abscld
    #
    wph
    @6
    @2
    c1
    @7
    wph
    c1
    @8
    rehalfcld
    @8
    wph
    cA
    cB
    dnibndlem12.2
    dnibndlem12.3
    dnibndlem11
    @2
    c1
    cle
    wbr
    #
    wph
    @2
    c1
    clt
    wbr
    #
    @11
    halflt1
    @2
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    wa
    @12
    @11
    wi
    @13
    @14
    halfre
    1re
    pm3.2i
    @2
    c1
    ltle
    ax-mp
    ax-mp
    a1i
    letrd
    wph
    c1
    @0
    @1
    @8
    @9
    @10
    wph
    cA
    cB
    dnibndlem12.2
    dnibndlem12.3
    dnibndlem12.4
    dnibndlem10
    wph
    @0
    @9
    leabsd
    letrd
    letrd
    wph
    vx
    cA
    cB
    @1
    cT
    dnibndlem12.1
    dnibndlem12.2
    dnibndlem12.3
    dnibndlem1
    mpbird
end
