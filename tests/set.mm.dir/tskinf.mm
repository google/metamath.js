include "ctsk.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "com.mm"
include "cr1.mm"
include "cima.mm"
include "cen.mm"
include "wbr.mm"
include "cdom.mm"
include "con0.mm"
include "cvv.mm"
include "wf1.mm"
include "wss.mm"
include "r111.mm"
include "omsson.mm"
include "omex.mm"
include "f1imaen.mm"
include "mp2an.mm"
include "ensymi.mm"
include "simpl.mm"
include "tskr1om.mm"
include "ssdomg.mm"
include "sylc.mm"
include "endomtr.mm"
include "sylancr.mm"

theorem tskinf
  let cT: class T


  assert |- ( ( T e. Tarski /\ T =/= (/) ) -> _om ~<_ T )

  proof
    cT
    ctsk
    wcel
    #
    cT
    c0
    wne
    #
    wa
    #
    com
    cr1
    com
    cima
    #
    cen
    wbr
    @3
    cT
    cdom
    wbr
    #
    com
    cT
    cdom
    wbr
    @3
    com
    con0
    cvv
    cr1
    wf1
    com
    con0
    wss
    @3
    com
    cen
    wbr
    r111
    omsson
    con0
    cvv
    com
    cr1
    omex
    f1imaen
    mp2an
    ensymi
    @2
    @0
    @3
    cT
    wss
    @4
    @0
    @1
    simpl
    cT
    tskr1om
    @3
    cT
    ctsk
    ssdomg
    sylc
    com
    @3
    cT
    endomtr
    sylancr
end
