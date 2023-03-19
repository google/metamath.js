include "cnx.mm"
include "cfv.mm"
include "cid.mm"
include "cn.mm"
include "cres.mm"
include "cvv.mm"
include "df-ndx.mm"
include "wcel.mm"
include "nnex.mm"
include "resiexg.mm"
include "ax-mp.mm"
include "eqeltri.mm"
include "strfvn.mm"
include "fveq1i.mm"
include "wceq.mm"
include "fvresi.mm"
include "3eqtri.mm"

theorem ndxarg
  let cE: class E
  let cN: class N
  assume ndxarg.1: |- E = Slot N
  assume ndxarg.2: |- N e. NN


  assert |- ( E ` ndx ) = N

  proof
    cnx
    cE
    cfv
    cN
    cnx
    cfv
    cN
    cid
    cn
    cres
    #
    cfv
    #
    cN
    cnx
    cE
    cN
    cnx
    @0
    cvv
    df-ndx
    cn
    cvv
    wcel
    @0
    cvv
    wcel
    nnex
    cn
    cvv
    resiexg
    ax-mp
    eqeltri
    ndxarg.1
    strfvn
    cN
    cnx
    @0
    df-ndx
    fveq1i
    cN
    cn
    wcel
    @1
    cN
    wceq
    ndxarg.2
    cn
    cN
    fvresi
    ax-mp
    3eqtri
end
