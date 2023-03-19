include "cgz.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "cc.mm"
include "cre.mm"
include "cz.mm"
include "cim.mm"
include "gzcn.mm"
include "cjcld.mm"
include "recjd.mm"
include "elgz.mm"
include "simp2bi.mm"
include "eqeltrd.mm"
include "cneg.mm"
include "imcjd.mm"
include "simp3bi.mm"
include "znegcld.mm"
include "syl3anbrc.mm"

theorem gzcjcl
  let cA: class A


  assert |- ( A e. Z[i] -> ( * ` A ) e. Z[i] )

  proof
    cA
    cgz
    wcel
    #
    cA
    ccj
    cfv
    #
    cc
    wcel
    @1
    cre
    cfv
    #
    cz
    wcel
    @1
    cim
    cfv
    #
    cz
    wcel
    @1
    cgz
    wcel
    @0
    cA
    cA
    gzcn
    #
    cjcld
    @0
    @2
    cA
    cre
    cfv
    #
    cz
    @0
    cA
    @4
    recjd
    @0
    cA
    cc
    wcel
    #
    @5
    cz
    wcel
    #
    cA
    cim
    cfv
    #
    cz
    wcel
    #
    cA
    elgz
    #
    simp2bi
    eqeltrd
    @0
    @3
    @8
    cneg
    cz
    @0
    cA
    @4
    imcjd
    @0
    @8
    @0
    @6
    @7
    @9
    @10
    simp3bi
    znegcld
    eqeltrd
    @1
    elgz
    syl3anbrc
end
