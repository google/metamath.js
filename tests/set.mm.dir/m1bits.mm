include "cn0.mm"
include "cc0.mm"
include "cbits.mm"
include "cfv.mm"
include "cdif.mm"
include "cneg.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cz.mm"
include "wcel.mm"
include "wceq.mm"
include "0z.mm"
include "bitscmp.mm"
include "ax-mp.mm"
include "c0.mm"
include "0bits.mm"
include "difeq2i.mm"
include "dif0.mm"
include "eqtri.mm"
include "neg0.mm"
include "oveq1i.mm"
include "df-neg.mm"
include "eqtr4i.mm"
include "fveq2i.mm"
include "3eqtr3ri.mm"

theorem m1bits



  assert |- ( bits ` -u 1 ) = NN0

  proof
    cn0
    cc0
    cbits
    cfv
    #
    cdif
    #
    cc0
    cneg
    #
    c1
    cmin
    co
    #
    cbits
    cfv
    #
    cn0
    c1
    cneg
    #
    cbits
    cfv
    cc0
    cz
    wcel
    @1
    @4
    wceq
    0z
    cc0
    bitscmp
    ax-mp
    @1
    cn0
    c0
    cdif
    cn0
    @0
    c0
    cn0
    0bits
    difeq2i
    cn0
    dif0
    eqtri
    @3
    @5
    cbits
    @3
    cc0
    c1
    cmin
    co
    @5
    @2
    cc0
    c1
    cmin
    neg0
    oveq1i
    c1
    df-neg
    eqtr4i
    fveq2i
    3eqtr3ri
end
