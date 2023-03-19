include "cbs.mm"
include "cnx.mm"
include "cfv.mm"
include "cop.mm"
include "2strstr1.mm"
include "baseid.mm"
include "csn.mm"
include "cpr.mm"
include "snsspr1.mm"
include "sseqtr4i.mm"
include "strfv.mm"

theorem 2strbas1
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cN: class N
  let cV: class V
  assume 2str1.g: |- G = { <. ( Base ` ndx ) , B >. , <. N , .+ >. }
  assume 2str1.b: |- ( Base ` ndx ) < N
  assume 2str1.n: |- N e. NN


  assert |- ( B e. V -> B = ( Base ` G ) )

  proof
    cB
    cG
    cbs
    cV
    cnx
    cbs
    cfv
    #
    cN
    cop
    cB
    c.pl
    cG
    cN
    2str1.g
    2str1.b
    2str1.n
    2strstr1
    baseid
    @0
    cB
    cop
    #
    csn
    @1
    cN
    c.pl
    cop
    #
    cpr
    cG
    @1
    @2
    snsspr1
    2str1.g
    sseqtr4i
    strfv
end
