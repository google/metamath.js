include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cun.mm"
include "csn.mm"
include "wceq.mm"
include "peano2uz.mm"
include "eluzfz2.mm"
include "syl.mm"
include "peano2fzr.mm"
include "mpdan.mm"
include "fzsplit.mm"
include "cz.mm"
include "eluzelz.mm"
include "fzsn.mm"
include "3syl.mm"
include "uneq2d.mm"
include "eqtrd.mm"

theorem fzsuc
  let cM: class M
  let cN: class N


  assert |- ( N e. ( ZZ>= ` M ) -> ( M ... ( N + 1 ) ) = ( ( M ... N ) u. { ( N + 1 ) } ) )

  proof
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    cM
    cN
    c1
    caddc
    co
    #
    cfz
    co
    #
    cM
    cN
    cfz
    co
    #
    @2
    @2
    cfz
    co
    #
    cun
    #
    @4
    @2
    csn
    #
    cun
    @1
    cN
    @3
    wcel
    #
    @3
    @6
    wceq
    @1
    @2
    @3
    wcel
    #
    @8
    @1
    @2
    @0
    wcel
    #
    @9
    cM
    cN
    peano2uz
    #
    cM
    @2
    eluzfz2
    syl
    cN
    cM
    @2
    peano2fzr
    mpdan
    cN
    cM
    @2
    fzsplit
    syl
    @1
    @5
    @7
    @4
    @1
    @10
    @2
    cz
    wcel
    @5
    @7
    wceq
    @11
    cM
    @2
    eluzelz
    @2
    fzsn
    3syl
    uneq2d
    eqtrd
end
