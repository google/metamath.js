include "cword.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "ccsh.mm"
include "wceq.mm"
include "cc.mm"
include "zcn.mm"
include "addcom.mm"
include "syl2anr.mm"
include "3adant1.mm"
include "oveq2d.mm"
include "2cshw.mm"
include "3com23.mm"
include "3eqtr4rd.mm"

theorem 2cshwcom
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ N e. ZZ /\ M e. ZZ ) -> ( ( W cyclShift N ) cyclShift M ) = ( ( W cyclShift M ) cyclShift N ) )

  proof
    cW
    cV
    cword
    wcel
    #
    cN
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    w3a
    #
    cW
    cM
    cN
    caddc
    co
    #
    ccsh
    co
    #
    cW
    cN
    cM
    caddc
    co
    #
    ccsh
    co
    cW
    cM
    ccsh
    co
    cN
    ccsh
    co
    #
    cW
    cN
    ccsh
    co
    cM
    ccsh
    co
    @3
    @4
    @6
    cW
    ccsh
    @1
    @2
    @4
    @6
    wceq
    #
    @0
    @2
    cM
    cc
    wcel
    cN
    cc
    wcel
    @8
    @1
    cM
    zcn
    cN
    zcn
    cM
    cN
    addcom
    syl2anr
    3adant1
    oveq2d
    @0
    @2
    @1
    @7
    @5
    wceq
    cM
    cN
    cV
    cW
    2cshw
    3com23
    cN
    cM
    cV
    cW
    2cshw
    3eqtr4rd
end
