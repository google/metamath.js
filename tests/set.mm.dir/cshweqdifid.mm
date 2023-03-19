include "cword.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "wa.mm"
include "ccsh.mm"
include "co.mm"
include "wceq.mm"
include "cmin.mm"
include "wi.mm"
include "id.mm"
include "ancli.mm"
include "anim1i.mm"
include "3impb.mm"
include "cshweqdif2.mm"
include "syl.mm"

theorem cshweqdifid
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ N e. ZZ /\ M e. ZZ ) -> ( ( W cyclShift N ) = ( W cyclShift M ) -> ( W cyclShift ( M - N ) ) = W ) )

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
    @0
    @0
    wa
    #
    @1
    @2
    wa
    #
    wa
    #
    cW
    cN
    ccsh
    co
    cW
    cM
    ccsh
    co
    wceq
    cW
    cM
    cN
    cmin
    co
    ccsh
    co
    cW
    wceq
    wi
    @0
    @1
    @2
    @5
    @0
    @3
    @4
    @0
    @0
    @0
    id
    ancli
    anim1i
    3impb
    cW
    cM
    cN
    cV
    cW
    cshweqdif2
    syl
end
