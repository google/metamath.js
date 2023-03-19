include "cgz.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cre.mm"
include "cim.mm"
include "caddc.mm"
include "cn0.mm"
include "gzcn.mm"
include "absvalsq2d.mm"
include "cz.mm"
include "cc.mm"
include "elgz.mm"
include "simp2bi.mm"
include "zsqcl2.mm"
include "syl.mm"
include "simp3bi.mm"
include "nn0addcld.mm"
include "eqeltrd.mm"

theorem gzabssqcl
  let cA: class A


  assert |- ( A e. Z[i] -> ( ( abs ` A ) ^ 2 ) e. NN0 )

  proof
    cA
    cgz
    wcel
    #
    cA
    cabs
    cfv
    c2
    cexp
    co
    cA
    cre
    cfv
    #
    c2
    cexp
    co
    #
    cA
    cim
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    cn0
    @0
    cA
    cA
    gzcn
    absvalsq2d
    @0
    @2
    @4
    @0
    @1
    cz
    wcel
    #
    @2
    cn0
    wcel
    @0
    cA
    cc
    wcel
    #
    @5
    @3
    cz
    wcel
    #
    cA
    elgz
    #
    simp2bi
    @1
    zsqcl2
    syl
    @0
    @7
    @4
    cn0
    wcel
    @0
    @6
    @5
    @7
    @8
    simp3bi
    @3
    zsqcl2
    syl
    nn0addcld
    eqeltrd
end
