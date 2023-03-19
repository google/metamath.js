include "cr.mm"
include "wcel.mm"
include "cneg.mm"
include "cfl.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "renegcl.mm"
include "reflcl.mm"
include "syl.mm"
include "wa.mm"
include "flle.mm"
include "adantr.mm"
include "lenegcon2.mm"
include "mpbird.mm"
include "mpdan.mm"

theorem ceige
  let cA: class A


  assert |- ( A e. RR -> A <_ -u ( |_ ` -u A ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cneg
    #
    cfl
    cfv
    #
    cr
    wcel
    #
    cA
    @2
    cneg
    cle
    wbr
    #
    @0
    @1
    cr
    wcel
    #
    @3
    cA
    renegcl
    #
    @1
    reflcl
    syl
    @0
    @3
    wa
    @4
    @2
    @1
    cle
    wbr
    #
    @0
    @7
    @3
    @0
    @5
    @7
    @6
    @1
    flle
    syl
    adantr
    cA
    @2
    lenegcon2
    mpbird
    mpdan
end
