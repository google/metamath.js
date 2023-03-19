include "ctsk.mm"
include "wcel.mm"
include "wtr.mm"
include "wa.mm"
include "cv.mm"
include "cuni.mm"
include "cpw.mm"
include "wral.mm"
include "cfn.mm"
include "cdif.mm"
include "wb.mm"
include "tskuni.mm"
include "3expia.mm"
include "wi.mm"
include "tskpw.mm"
include "ex.mm"
include "adantr.mm"
include "jcad.mm"
include "ralrimiv.mm"
include "pwinfig.mm"
include "syl.mm"

theorem pwinfi3
  let cA: class A
  let cT: class T
  let vx: setvar x


  assert |- ( ( T e. Tarski /\ Tr T ) -> ( A e. ( T \ Fin ) <-> ~P A e. ( T \ Fin ) ) )

  proof
    cT
    ctsk
    wcel
    #
    cT
    wtr
    #
    wa
    #
    vx
    cv
    #
    cuni
    cT
    wcel
    #
    @3
    cpw
    cT
    wcel
    #
    wa
    #
    vx
    cT
    wral
    cA
    cT
    cfn
    cdif
    #
    wcel
    cA
    cpw
    @7
    wcel
    wb
    @2
    @6
    vx
    cT
    @2
    @3
    cT
    wcel
    #
    @4
    @5
    @0
    @1
    @8
    @4
    @3
    cT
    tskuni
    3expia
    @0
    @8
    @5
    wi
    @1
    @0
    @8
    @5
    @3
    cT
    tskpw
    ex
    adantr
    jcad
    ralrimiv
    vx
    cA
    cT
    pwinfig
    syl
end
