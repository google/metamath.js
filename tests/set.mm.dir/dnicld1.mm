include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cfl.mm"
include "cfv.mm"
include "cmin.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "halfre.mm"
include "a1i.mm"
include "jca.mm"
include "readdcl.mm"
include "syl.mm"
include "reflcl.mm"
include "recnd.mm"
include "subcld.mm"
include "abscld.mm"

theorem dnicld1
  let wph: wff ph
  let cA: class A
  assume dnicld1.1: |- ( ph -> A e. RR )


  assert |- ( ph -> ( abs ` ( ( |_ ` ( A + ( 1 / 2 ) ) ) - A ) ) e. RR )

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
    cA
    cmin
    co
    wph
    @2
    cA
    wph
    @2
    wph
    @1
    cr
    wcel
    #
    @2
    cr
    wcel
    wph
    cA
    cr
    wcel
    #
    @0
    cr
    wcel
    #
    wa
    @3
    wph
    @4
    @5
    dnicld1.1
    @5
    wph
    halfre
    a1i
    jca
    cA
    @0
    readdcl
    syl
    @1
    reflcl
    syl
    recnd
    wph
    cA
    dnicld1.1
    recnd
    subcld
    abscld
end
