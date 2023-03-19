include "cale.mm"
include "con0.mm"
include "wfn.mm"
include "char.mm"
include "com.mm"
include "crdg.mm"
include "rdgfnon.mm"
include "df-aleph.mm"
include "fneq1i.mm"
include "mpbir.mm"

theorem alephfnon



  assert |- aleph Fn On

  proof
    cale
    con0
    wfn
    char
    com
    crdg
    #
    con0
    wfn
    com
    char
    rdgfnon
    con0
    cale
    @0
    df-aleph
    fneq1i
    mpbir
end
