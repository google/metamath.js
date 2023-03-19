include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "abscl.mm"
include "absge0.mm"
include "absid.mm"
include "syl2anc.mm"

theorem absidm
  let cA: class A


  assert |- ( A e. CC -> ( abs ` ( abs ` A ) ) = ( abs ` A ) )

  proof
    cA
    cc
    wcel
    cA
    cabs
    cfv
    #
    cr
    wcel
    cc0
    @0
    cle
    wbr
    @0
    cabs
    cfv
    @0
    wceq
    cA
    abscl
    cA
    absge0
    @0
    absid
    syl2anc
end
