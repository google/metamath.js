include "cz.mm"
include "wcel.mm"
include "cgz.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "zgz.mm"
include "igz.mm"
include "gzmulcl.mm"
include "sylancr.mm"
include "gzaddcl.mm"
include "syl2an.mm"

theorem gzreim
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ZZ /\ B e. ZZ ) -> ( A + ( _i x. B ) ) e. Z[i] )

  proof
    cA
    cz
    wcel
    cA
    cgz
    wcel
    ci
    cB
    cmul
    co
    #
    cgz
    wcel
    #
    cA
    @0
    caddc
    co
    cgz
    wcel
    cB
    cz
    wcel
    #
    cA
    zgz
    @2
    ci
    cgz
    wcel
    cB
    cgz
    wcel
    @1
    igz
    cB
    zgz
    ci
    cB
    gzmulcl
    sylancr
    cA
    @0
    gzaddcl
    syl2an
end
