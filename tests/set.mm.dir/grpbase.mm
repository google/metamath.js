include "cplusg.mm"
include "c2.mm"
include "df-plusg.mm"
include "1lt2.mm"
include "2nn.mm"
include "2strbas.mm"

theorem grpbase
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cV: class V
  assume grpfn.g: |- G = { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. }


  assert |- ( B e. V -> B = ( Base ` G ) )

  proof
    cB
    c.pl
    cplusg
    cG
    c2
    cV
    grpfn.g
    df-plusg
    1lt2
    2nn
    2strbas
end
