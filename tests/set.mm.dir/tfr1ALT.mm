include "con0.mm"
include "cep.mm"
include "epweon.mm"
include "epse.mm"
include "crecs.mm"
include "cwrecs.mm"
include "df-recs.mm"
include "eqtri.mm"
include "wfr1.mm"

theorem tfr1ALT
  let cF: class F
  let cG: class G
  assume tfrALT.1: |- F = recs ( G )


  assert |- F Fn On

  proof
    con0
    cep
    cF
    cG
    epweon
    con0
    epse
    cF
    cG
    crecs
    con0
    cep
    cG
    cwrecs
    tfrALT.1
    cG
    df-recs
    eqtri
    wfr1
end
