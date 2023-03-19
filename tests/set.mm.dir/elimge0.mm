include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "breq2.mm"
include "0re.mm"
include "leidi.mm"
include "elimhyp.mm"

theorem elimge0
  let cA: class A


  assert |- 0 <_ if ( 0 <_ A , A , 0 )

  proof
    cc0
    cA
    cle
    wbr
    #
    cc0
    @0
    cA
    cc0
    cif
    #
    cle
    wbr
    cc0
    cc0
    cle
    wbr
    cA
    cc0
    cA
    @1
    cc0
    cle
    breq2
    cc0
    @1
    cc0
    cle
    breq2
    cc0
    0re
    leidi
    elimhyp
end
