include "crecs.mm"
include "con0.mm"
include "cep.mm"
include "cwrecs.mm"
include "df-recs.mm"
include "nfcv.mm"
include "nfwrecs.mm"
include "nfcxfr.mm"

theorem nfrecs
  let vx: setvar x
  let cF: class F
  assume nfrecs.f: |- F/_ x F


  assert |- F/_ x recs ( F )

  proof
    vx
    cF
    crecs
    con0
    cep
    cF
    cwrecs
    cF
    df-recs
    vx
    con0
    cep
    cF
    vx
    cep
    nfcv
    vx
    con0
    nfcv
    nfrecs.f
    nfwrecs
    nfcxfr
end
