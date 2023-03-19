include "citg.mm"
include "cv.mm"
include "wcel.mm"
include "cc0.mm"
include "cif.mm"
include "cle.mm"
include "wss.mm"
include "wceq.mm"
include "itgss2.mm"
include "syl.mm"
include "cr.mm"
include "cmpt.mm"
include "cibl.mm"
include "cmbf.mm"
include "iblmbf.mm"
include "mbfdm2.mm"
include "wa.mm"
include "sselda.mm"
include "syldan.mm"
include "0re.mm"
include "ifcl.mm"
include "sylancl.mm"
include "cdif.mm"
include "wn.mm"
include "eldifn.mm"
include "adantl.mm"
include "iffalsed.mm"
include "iftrue.mm"
include "mpteq2ia.mm"
include "iblss.mm"
include "syl5eqel.mm"
include "iblss2.mm"
include "wbr.mm"
include "leidd.mm"
include "breq1.mm"
include "ifboth.mm"
include "syl2anc.mm"
include "itgle.mm"
include "eqbrtrd.mm"

theorem itgless
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume itgless.1: |- ( ph -> A C_ B )
  assume itgless.2: |- ( ph -> A e. dom vol )
  assume itgless.3: |- ( ( ph /\ x e. B ) -> C e. RR )
  assume itgless.4: |- ( ( ph /\ x e. B ) -> 0 <_ C )
  assume itgless.5: |- ( ph -> ( x e. B |-> C ) e. L^1 )

  disjoint A x
  disjoint B x
  disjoint ph x
  assert |- ( ph -> S. A C _d x <_ S. B C _d x )

  proof
    wph
    vx
    cA
    cC
    citg
    #
    vx
    cB
    vx
    cv
    #
    cA
    wcel
    #
    cC
    cc0
    cif
    #
    citg
    #
    vx
    cB
    cC
    citg
    cle
    wph
    cA
    cB
    wss
    @0
    @4
    wceq
    itgless.1
    vx
    cA
    cB
    cC
    itgss2
    syl
    wph
    vx
    cB
    @3
    cC
    wph
    vx
    cA
    cB
    @3
    cr
    itgless.1
    wph
    vx
    cB
    cC
    cr
    wph
    vx
    cB
    cC
    cmpt
    #
    cibl
    wcel
    @5
    cmbf
    wcel
    itgless.5
    @5
    iblmbf
    syl
    itgless.3
    mbfdm2
    wph
    @2
    wa
    cC
    cr
    wcel
    #
    cc0
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    wph
    @2
    @1
    cB
    wcel
    #
    @6
    wph
    cA
    cB
    @1
    itgless.1
    sselda
    itgless.3
    syldan
    0re
    @2
    cC
    cc0
    cr
    ifcl
    #
    sylancl
    wph
    @1
    cB
    cA
    cdif
    wcel
    #
    wa
    @2
    cC
    cc0
    @11
    @2
    wn
    wph
    @1
    cB
    cA
    eldifn
    adantl
    iffalsed
    wph
    vx
    cA
    @3
    cmpt
    vx
    cA
    cC
    cmpt
    cibl
    vx
    cA
    @3
    cC
    @2
    cC
    cc0
    iftrue
    mpteq2ia
    wph
    vx
    cA
    cB
    cC
    cr
    itgless.1
    itgless.2
    itgless.3
    itgless.5
    iblss
    syl5eqel
    iblss2
    itgless.5
    wph
    @9
    wa
    #
    @6
    @7
    @8
    itgless.3
    0re
    @10
    sylancl
    itgless.3
    @12
    cC
    cC
    cle
    wbr
    #
    cc0
    cC
    cle
    wbr
    #
    @3
    cC
    cle
    wbr
    #
    @12
    cC
    itgless.3
    leidd
    itgless.4
    @2
    @13
    @14
    @15
    cC
    cc0
    cC
    @3
    cC
    cle
    breq1
    cc0
    @3
    cC
    cle
    breq1
    ifboth
    syl2anc
    itgle
    eqbrtrd
end
