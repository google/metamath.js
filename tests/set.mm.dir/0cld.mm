include "ctop.mm"
include "wcel.mm"
include "c0.mm"
include "ccld.mm"
include "cfv.mm"
include "cuni.mm"
include "cdif.mm"
include "dif0.mm"
include "topopn.mm"
include "wss.mm"
include "wb.mm"
include "0ss.mm"
include "eqid.mm"
include "iscld2.mm"
include "mpan2.mm"
include "mpbird.mm"

theorem 0cld
  let cJ: class J


  assert |- ( J e. Top -> (/) e. ( Clsd ` J ) )

  proof
    cJ
    ctop
    wcel
    #
    c0
    cJ
    ccld
    cfv
    wcel
    #
    cJ
    cuni
    #
    c0
    cdif
    #
    cJ
    wcel
    #
    cJ
    @3
    @2
    dif0
    topopn
    @0
    c0
    @2
    wss
    @1
    @4
    wb
    @2
    0ss
    c0
    cJ
    @2
    @2
    eqid
    iscld2
    mpan2
    mpbird
end
