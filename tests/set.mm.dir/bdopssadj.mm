include "cbo.mm"
include "clo.mm"
include "ccop.mm"
include "cin.mm"
include "cado.mm"
include "cdm.mm"
include "lncnbd.mm"
include "cnlnssadj.mm"
include "eqsstr3i.mm"

theorem bdopssadj



  assert |- BndLinOp C_ dom adjh

  proof
    cbo
    clo
    ccop
    cin
    cado
    cdm
    lncnbd
    cnlnssadj
    eqsstr3i
end
