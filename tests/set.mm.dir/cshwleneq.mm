include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cz.mm"
include "ccsh.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "chash.mm"
include "cfv.mm"
include "cshwlen.mm"
include "ad2ant2r.mm"
include "eqcomd.mm"
include "3adant3.mm"
include "fveq2.mm"
include "3ad2ant3.mm"
include "ad2ant2l.mm"
include "3eqtrd.mm"

theorem cshwleneq
  let cU: class U
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W


  assert |- ( ( ( W e. Word V /\ U e. Word V ) /\ ( N e. ZZ /\ M e. ZZ ) /\ ( W cyclShift N ) = ( U cyclShift M ) ) -> ( # ` W ) = ( # ` U ) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cU
    @0
    wcel
    #
    wa
    #
    cN
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    wa
    #
    cW
    cN
    ccsh
    co
    #
    cU
    cM
    ccsh
    co
    #
    wceq
    #
    w3a
    cW
    chash
    cfv
    #
    @7
    chash
    cfv
    #
    @8
    chash
    cfv
    #
    cU
    chash
    cfv
    #
    @3
    @6
    @10
    @11
    wceq
    @9
    @3
    @6
    wa
    @11
    @10
    @1
    @4
    @11
    @10
    wceq
    @2
    @5
    cN
    cV
    cW
    cshwlen
    ad2ant2r
    eqcomd
    3adant3
    @9
    @3
    @11
    @12
    wceq
    @6
    @7
    @8
    chash
    fveq2
    3ad2ant3
    @3
    @6
    @12
    @13
    wceq
    #
    @9
    @2
    @5
    @14
    @1
    @4
    cM
    cV
    cU
    cshwlen
    ad2ant2l
    3adant3
    3eqtrd
end
