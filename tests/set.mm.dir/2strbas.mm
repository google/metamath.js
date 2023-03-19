include "cbs.mm"
include "c1.mm"
include "cop.mm"
include "2strstr.mm"
include "baseid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "cpr.mm"
include "snsspr1.mm"
include "sseqtr4i.mm"
include "strfv.mm"

theorem 2strbas
  let cB: class B
  let c.pl: class .+
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  assume 2str.g: |- G = { <. ( Base ` ndx ) , B >. , <. ( E ` ndx ) , .+ >. }
  assume 2str.e: |- E = Slot N
  assume 2str.l: |- 1 < N
  assume 2str.n: |- N e. NN


  assert |- ( B e. V -> B = ( Base ` G ) )

  proof
    cB
    cG
    cbs
    cV
    c1
    cN
    cop
    cB
    c.pl
    cE
    cG
    cN
    2str.g
    2str.e
    2str.l
    2str.n
    2strstr
    baseid
    cnx
    cbs
    cfv
    cB
    cop
    #
    csn
    @0
    cnx
    cE
    cfv
    c.pl
    cop
    #
    cpr
    cG
    @0
    @1
    snsspr1
    2str.g
    sseqtr4i
    strfv
end
