include "cn.mm"
include "cvv.mm"
include "wcel.mm"
include "cnx.mm"
include "cfv.mm"
include "wceq.mm"
include "nnex.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "cslot.mm"
include "df-ndx.mm"
include "fveq12i.mm"
include "bj-evalid.mm"
include "syl5eq.mm"
include "mp2an.mm"

theorem bj-ndxarg
  let cE: class E
  let cN: class N
  assume bj-ndxarg.1: |- E = Slot N
  assume bj-ndxarg.2: |- N e. NN


  assert |- ( E ` ndx ) = N

  proof
    cn
    cvv
    wcel
    #
    cN
    cn
    wcel
    #
    cnx
    cE
    cfv
    #
    cN
    wceq
    nnex
    bj-ndxarg.2
    @0
    @1
    wa
    @2
    cid
    cn
    cres
    #
    cN
    cslot
    #
    cfv
    cN
    cnx
    @3
    cE
    @4
    bj-ndxarg.1
    df-ndx
    fveq12i
    cN
    cn
    cvv
    bj-evalid
    syl5eq
    mp2an
end
