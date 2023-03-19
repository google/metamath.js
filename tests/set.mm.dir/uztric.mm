include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cuz.mm"
include "cfv.mm"
include "wo.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "zre.mm"
include "letric.mm"
include "syl2an.mm"
include "eluz.mm"
include "wb.mm"
include "ancoms.mm"
include "orbi12d.mm"
include "mpbird.mm"

theorem uztric
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( N e. ( ZZ>= ` M ) \/ M e. ( ZZ>= ` N ) ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cN
    cM
    cuz
    cfv
    wcel
    #
    cM
    cN
    cuz
    cfv
    wcel
    #
    wo
    cM
    cN
    cle
    wbr
    #
    cN
    cM
    cle
    wbr
    #
    wo
    #
    @0
    cM
    cr
    wcel
    cN
    cr
    wcel
    @7
    @1
    cM
    zre
    cN
    zre
    cM
    cN
    letric
    syl2an
    @2
    @3
    @5
    @4
    @6
    cM
    cN
    eluz
    @1
    @0
    @4
    @6
    wb
    cN
    cM
    eluz
    ancoms
    orbi12d
    mpbird
end
