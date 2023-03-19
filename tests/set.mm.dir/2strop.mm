include "c1.mm"
include "cop.mm"
include "2strstr.mm"
include "ndxid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "cbs.mm"
include "cpr.mm"
include "snsspr2.mm"
include "sseqtr4i.mm"
include "strfv.mm"

theorem 2strop
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


  assert |- ( .+ e. V -> .+ = ( E ` G ) )

  proof
    c.pl
    cG
    cE
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
    cE
    cN
    2str.e
    2str.n
    ndxid
    cnx
    cE
    cfv
    c.pl
    cop
    #
    csn
    cnx
    cbs
    cfv
    cB
    cop
    #
    @0
    cpr
    cG
    @1
    @0
    snsspr2
    2str.g
    sseqtr4i
    strfv
end
