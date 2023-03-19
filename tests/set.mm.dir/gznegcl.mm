include "cgz.mm"
include "wcel.mm"
include "cneg.mm"
include "cc.mm"
include "cre.mm"
include "cfv.mm"
include "cz.mm"
include "cim.mm"
include "gzcn.mm"
include "negcld.mm"
include "renegd.mm"
include "elgz.mm"
include "simp2bi.mm"
include "znegcld.mm"
include "eqeltrd.mm"
include "imnegd.mm"
include "simp3bi.mm"
include "syl3anbrc.mm"

theorem gznegcl
  let cA: class A


  assert |- ( A e. Z[i] -> -u A e. Z[i] )

  proof
    cA
    cgz
    wcel
    #
    cA
    cneg
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
    negcld
    @0
    @2
    cA
    cre
    cfv
    #
    cneg
    cz
    @0
    cA
    @4
    renegd
    @0
    @5
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
    znegcld
    eqeltrd
    @0
    @3
    @8
    cneg
    cz
    @0
    cA
    @4
    imnegd
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
