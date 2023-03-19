include "cv.mm"
include "cpj.mm"
include "cfv.mm"
include "cdm.mm"
include "ccss.mm"
include "wceq.mm"
include "cphl.mm"
include "chs.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "dmeqd.mm"
include "eqeq12d.mm"
include "df-hil.mm"
include "elrab2.mm"

theorem ishil
  let cC: class C
  let cH: class H
  let cK: class K
  let vh: setvar h
  assume ishil.k: |- K = ( proj ` H )
  assume ishil.c: |- C = ( CSubSp ` H )


  assert |- ( H e. Hil <-> ( H e. PreHil /\ dom K = C ) )

  proof
    vh
    cv
    #
    cpj
    cfv
    #
    cdm
    #
    @0
    ccss
    cfv
    #
    wceq
    cK
    cdm
    #
    cC
    wceq
    vh
    cH
    cphl
    chs
    @0
    cH
    wceq
    #
    @2
    @4
    @3
    cC
    @5
    @1
    cK
    @5
    @1
    cH
    cpj
    cfv
    cK
    @0
    cH
    cpj
    fveq2
    ishil.k
    syl6eqr
    dmeqd
    @5
    @3
    cH
    ccss
    cfv
    cC
    @0
    cH
    ccss
    fveq2
    ishil.c
    syl6eqr
    eqeq12d
    vh
    df-hil
    elrab2
end
