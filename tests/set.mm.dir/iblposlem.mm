include "cr.mm"
include "cv.mm"
include "wcel.mm"
include "cc0.mm"
include "cneg.mm"
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
include "le0neg2d.mm"
include "mpbid.mm"
include "adantrr.mm"
include "simprr.mm"
include "wb.mm"
include "renegcld.mm"
include "0re.mm"
include "letri3.mm"
include "sylancl.mm"
include "mpbir2and.mm"
include "ifeq1da.mm"
include "ifid.mm"
include "syl6eq.mm"
include "mpteq2dv.mm"
include "fconstmpt.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "itg20.mm"

theorem iblposlem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume iblrelem.1: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume iblpos.2: |- ( ( ph /\ x e. A ) -> 0 <_ B )

  disjoint A x
  disjoint ph x
  assert |- ( ph -> ( S.2 ` ( x e. RR |-> if ( ( x e. A /\ 0 <_ -u B ) , -u B , 0 ) ) ) = 0 )

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
    cneg
    #
    cle
    wbr
    #
    wa
    #
    @1
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
    @5
    @6
    citg2
    wph
    @5
    vx
    cr
    cc0
    cmpt
    @6
    wph
    vx
    cr
    @4
    cc0
    wph
    @4
    @3
    cc0
    cc0
    cif
    cc0
    wph
    @3
    @1
    cc0
    cc0
    wph
    @3
    wa
    #
    @1
    cc0
    wceq
    #
    @1
    cc0
    cle
    wbr
    #
    @2
    wph
    @0
    @9
    @2
    wph
    @0
    wa
    #
    cc0
    cB
    cle
    wbr
    @9
    iblpos.2
    @10
    cB
    iblrelem.1
    le0neg2d
    mpbid
    adantrr
    wph
    @0
    @2
    simprr
    @7
    @1
    cr
    wcel
    cc0
    cr
    wcel
    @8
    @9
    @2
    wa
    wb
    @7
    cB
    wph
    @0
    cB
    cr
    wcel
    @2
    iblrelem.1
    adantrr
    renegcld
    0re
    @1
    cc0
    letri3
    sylancl
    mpbir2and
    ifeq1da
    @3
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
