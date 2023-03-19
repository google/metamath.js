include "cn0.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cn.mm"
include "cun.mm"
include "df-n0.mm"
include "difeq1i.mm"
include "difun2.mm"
include "wcel.mm"
include "wn.mm"
include "wceq.mm"
include "0nnn.mm"
include "difsn.mm"
include "ax-mp.mm"
include "3eqtrri.mm"

theorem dfn2



  assert |- NN = ( NN0 \ { 0 } )

  proof
    cn0
    cc0
    csn
    #
    cdif
    cn
    @0
    cun
    #
    @0
    cdif
    cn
    @0
    cdif
    #
    cn
    cn0
    @1
    @0
    df-n0
    difeq1i
    cn
    @0
    difun2
    cc0
    cn
    wcel
    wn
    @2
    cn
    wceq
    0nnn
    cc0
    cn
    difsn
    ax-mp
    3eqtrri
end
