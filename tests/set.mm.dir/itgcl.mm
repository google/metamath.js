include "citg.mm"
include "cc0.mm"
include "c3.mm"
include "cfz.mm"
include "co.mm"
include "ci.mm"
include "cv.mm"
include "cexp.mm"
include "cr.mm"
include "wcel.mm"
include "cdiv.mm"
include "cre.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cif.mm"
include "cmpt.mm"
include "citg2.mm"
include "cmul.mm"
include "csu.mm"
include "cc.mm"
include "eqid.mm"
include "dfitg.mm"
include "fzfid.mm"
include "cn0.mm"
include "ax-icn.mm"
include "elfznn0.mm"
include "adantl.mm"
include "expcl.mm"
include "sylancr.mm"
include "cz.mm"
include "elfzelz.mm"
include "eqidd.mm"
include "iblitg.mm"
include "sylan2.mm"
include "recnd.mm"
include "mulcld.mm"
include "fsumcl.mm"
include "syl5eqel.mm"

theorem itgcl
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vk: setvar k
  let vy: setvar y
  assume itgmpt.1: |- ( ( ph /\ x e. A ) -> B e. V )
  assume itgcl.2: |- ( ph -> ( x e. A |-> B ) e. L^1 )

  disjoint A x
  disjoint ph x
  disjoint V x
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint x y
  disjoint A y
  disjoint B k
  disjoint B y
  disjoint k ph
  assert |- ( ph -> S. A B _d x e. CC )

  proof
    wph
    vx
    cA
    cB
    citg
    cc0
    c3
    cfz
    co
    #
    ci
    vk
    cv
    #
    cexp
    co
    #
    vx
    cr
    vx
    cv
    cA
    wcel
    #
    cc0
    cB
    @2
    cdiv
    co
    cre
    cfv
    #
    cle
    wbr
    wa
    @4
    cc0
    cif
    cmpt
    #
    citg2
    cfv
    #
    cmul
    co
    #
    vk
    csu
    cc
    vx
    cA
    cB
    @4
    vk
    @4
    eqid
    dfitg
    wph
    @0
    @7
    vk
    wph
    cc0
    c3
    fzfid
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @2
    @6
    @9
    ci
    cc
    wcel
    @1
    cn0
    wcel
    #
    @2
    cc
    wcel
    ax-icn
    @8
    @10
    wph
    @1
    c3
    elfznn0
    adantl
    ci
    @1
    expcl
    sylancr
    @9
    @6
    @8
    wph
    @1
    cz
    wcel
    @6
    cr
    wcel
    @1
    cc0
    c3
    elfzelz
    wph
    vx
    cA
    cB
    @4
    @5
    @1
    cV
    wph
    @5
    eqidd
    wph
    @3
    wa
    @4
    eqidd
    itgcl.2
    itgmpt.1
    iblitg
    sylan2
    recnd
    mulcld
    fsumcl
    syl5eqel
end
