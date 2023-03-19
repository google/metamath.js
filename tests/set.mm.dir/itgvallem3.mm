include "cr.mm"
include "cv.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cif.mm"
include "cmpt.mm"
include "citg2.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "adantrr.mm"
include "ifeq1da.mm"
include "ifid.mm"
include "syl6eq.mm"
include "mpteq2dv.mm"
include "fconstmpt.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "itg20.mm"

theorem itgvallem3
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume itgvallem3.1: |- ( ( ph /\ x e. A ) -> B = 0 )

  disjoint ph x
  assert |- ( ph -> ( S.2 ` ( x e. RR |-> if ( ( x e. A /\ 0 <_ B ) , B , 0 ) ) ) = 0 )

  proof
    wph
    vx
    cr
    vx
    cv
    cA
    wcel
    #
    cc0
    cB
    cle
    wbr
    #
    wa
    #
    cB
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    cr
    cc0
    csn
    cxp
    #
    citg2
    cfv
    cc0
    wph
    @4
    @5
    citg2
    wph
    @4
    vx
    cr
    cc0
    cmpt
    @5
    wph
    vx
    cr
    @3
    cc0
    wph
    @3
    @2
    cc0
    cc0
    cif
    cc0
    wph
    @2
    cB
    cc0
    cc0
    wph
    @0
    cB
    cc0
    wceq
    @1
    itgvallem3.1
    adantrr
    ifeq1da
    @2
    cc0
    ifid
    syl6eq
    mpteq2dv
    vx
    cr
    cc0
    fconstmpt
    syl6eqr
    fveq2d
    itg20
    syl6eq
end
