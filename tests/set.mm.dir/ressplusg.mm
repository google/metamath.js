include "cplusg.mm"
include "c2.mm"
include "df-plusg.mm"
include "2nn.mm"
include "1lt2.mm"
include "resslem.mm"

theorem ressplusg
  let cA: class A
  let c.pl: class .+
  let cG: class G
  let cH: class H
  let cV: class V
  assume ressplusg.1: |- H = ( G |`s A )
  assume ressplusg.2: |- .+ = ( +g ` G )


  assert |- ( A e. V -> .+ = ( +g ` H ) )

  proof
    cA
    c.pl
    cH
    cplusg
    c2
    cV
    cG
    ressplusg.1
    ressplusg.2
    df-plusg
    2nn
    1lt2
    resslem
end
