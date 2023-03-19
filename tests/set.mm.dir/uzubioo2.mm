include "cv.mm"
include "wcel.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "wrex.mm"
include "cr.mm"
include "wral.mm"
include "wa.mm"
include "cz.mm"
include "adantr.mm"
include "simpr.mm"
include "uzubioo.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "oveq1.mm"
include "rexeqdv.mm"
include "cbvralv.mm"
include "sylibr.mm"

theorem uzubioo2
  let wph: wff ph
  let vx: setvar x
  let vk: setvar k
  let cM: class M
  let cZ: class Z
  let vy: setvar y
  assume uzubioo2.1: |- ( ph -> M e. ZZ )
  assume uzubioo2.2: |- Z = ( ZZ>= ` M )

  disjoint M k
  disjoint Z k
  disjoint Z x
  disjoint k x
  disjoint Z y
  disjoint k y
  disjoint x y
  disjoint ph y
  assert |- ( ph -> A. x e. RR E. k e. ( x (,) +oo ) k e. Z )

  proof
    wph
    vk
    cv
    cZ
    wcel
    #
    vk
    vy
    cv
    #
    cpnf
    cioo
    co
    #
    wrex
    #
    vy
    cr
    wral
    @0
    vk
    vx
    cv
    #
    cpnf
    cioo
    co
    #
    wrex
    #
    vx
    cr
    wral
    wph
    @3
    vy
    cr
    wph
    @1
    cr
    wcel
    #
    wa
    vk
    cM
    @1
    cZ
    wph
    cM
    cz
    wcel
    @7
    uzubioo2.1
    adantr
    uzubioo2.2
    wph
    @7
    simpr
    uzubioo
    ralrimiva
    @6
    @3
    vx
    vy
    cr
    @4
    @1
    wceq
    @0
    vk
    @5
    @2
    @4
    @1
    cpnf
    cioo
    oveq1
    rexeqdv
    cbvralv
    sylibr
end
