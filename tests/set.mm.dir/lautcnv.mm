include "wcel.mm"
include "wa.mm"
include "ccnv.mm"
include "cbs.mm"
include "cfv.mm"
include "wf1o.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "wb.mm"
include "wral.mm"
include "eqid.mm"
include "laut1o.mm"
include "f1ocnv.mm"
include "syl.mm"
include "lautcnvle.mm"
include "ralrimivva.mm"
include "islaut.mm"
include "adantr.mm"
include "mpbir2and.mm"

theorem lautcnv
  let cF: class F
  let cI: class I
  let cK: class K
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume lautcnv.i: |- I = ( LAut ` K )


  assert |- ( ( K e. V /\ F e. I ) -> `' F e. I )

  proof
    cK
    cV
    wcel
    #
    cF
    cI
    wcel
    #
    wa
    #
    cF
    ccnv
    #
    cI
    wcel
    #
    cK
    cbs
    cfv
    #
    @5
    @3
    wf1o
    #
    vx
    cv
    #
    vy
    cv
    #
    cK
    cple
    cfv
    #
    wbr
    @7
    @3
    cfv
    @8
    @3
    cfv
    @9
    wbr
    wb
    #
    vy
    @5
    wral
    vx
    @5
    wral
    #
    @2
    @5
    @5
    cF
    wf1o
    @6
    cV
    @5
    cF
    cI
    cK
    @5
    eqid
    #
    lautcnv.i
    laut1o
    @5
    @5
    cF
    f1ocnv
    syl
    @2
    @10
    vx
    vy
    @5
    @5
    @5
    cF
    cI
    cK
    @9
    cV
    @7
    @8
    @12
    @9
    eqid
    #
    lautcnv.i
    lautcnvle
    ralrimivva
    @0
    @4
    @6
    @11
    wa
    wb
    @1
    vx
    vy
    cV
    @5
    @3
    cI
    cK
    @9
    @12
    @13
    lautcnv.i
    islaut
    adantr
    mpbir2and
end
