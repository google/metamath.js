include "cplusg.mm"
include "c2.mm"
include "df-plusg.mm"
include "1lt2.mm"
include "2nn.mm"
include "2strstr.mm"

theorem grpstr
  let cB: class B
  let c.pl: class .+
  let cG: class G
  assume grpfn.g: |- G = { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. }


  assert |- G Struct <. 1 , 2 >.

  proof
    cB
    c.pl
    cplusg
    cG
    c2
    grpfn.g
    df-plusg
    1lt2
    2nn
    2strstr
end
