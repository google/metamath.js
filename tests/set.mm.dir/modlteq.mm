include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cmo.mm"
include "zmodidfzoimp.mm"
include "eqeqan12d.mm"

theorem modlteq
  let cI: class I
  let cJ: class J
  let cN: class N


  assert |- ( ( I e. ( 0 ..^ N ) /\ J e. ( 0 ..^ N ) ) -> ( ( I mod N ) = ( J mod N ) <-> I = J ) )

  proof
    cI
    cc0
    cN
    cfzo
    co
    #
    wcel
    cJ
    @0
    wcel
    cI
    cN
    cmo
    co
    cI
    cJ
    cN
    cmo
    co
    cJ
    cI
    cN
    zmodidfzoimp
    cJ
    cN
    zmodidfzoimp
    eqeqan12d
end
