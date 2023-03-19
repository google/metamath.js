include "cn0.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cuz.mm"
include "cfv.mm"
include "simpr.mm"
include "nn0z.mm"
include "zaddcl.mm"
include "sylan.mm"
include "cr.mm"
include "zre.mm"
include "nn0addge2.mm"
include "ancoms.mm"
include "eluz2.mm"
include "syl3anbrc.mm"

theorem nn0pzuz
  let cN: class N
  let cZ: class Z


  assert |- ( ( N e. NN0 /\ Z e. ZZ ) -> ( N + Z ) e. ( ZZ>= ` Z ) )

  proof
    cN
    cn0
    wcel
    #
    cZ
    cz
    wcel
    #
    wa
    @1
    cN
    cZ
    caddc
    co
    #
    cz
    wcel
    #
    cZ
    @2
    cle
    wbr
    #
    @2
    cZ
    cuz
    cfv
    wcel
    @0
    @1
    simpr
    @0
    cN
    cz
    wcel
    @1
    @3
    cN
    nn0z
    cN
    cZ
    zaddcl
    sylan
    @1
    @0
    @4
    @1
    cZ
    cr
    wcel
    @0
    @4
    cZ
    zre
    cZ
    cN
    nn0addge2
    sylan
    ancoms
    cZ
    @2
    eluz2
    syl3anbrc
end
