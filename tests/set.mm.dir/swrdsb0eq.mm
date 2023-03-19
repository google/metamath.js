include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cn0.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cop.mm"
include "csubstr.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "cz.mm"
include "wi.mm"
include "simpll.mm"
include "nn0z.mm"
include "ad2antrl.mm"
include "adantl.mm"
include "swrdlend.mm"
include "syl3anc.mm"
include "3impia.mm"
include "simplr.mm"
include "eqtr4d.mm"

theorem swrdsb0eq
  let cU: class U
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W


  assert |- ( ( ( W e. Word V /\ U e. Word V ) /\ ( M e. NN0 /\ N e. NN0 ) /\ N <_ M ) -> ( W substr <. M , N >. ) = ( U substr <. M , N >. ) )

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
    cM
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cN
    cM
    cle
    wbr
    #
    w3a
    cW
    cM
    cN
    cop
    #
    csubstr
    co
    #
    c0
    cU
    @8
    csubstr
    co
    #
    @3
    @6
    @7
    @9
    c0
    wceq
    #
    @3
    @6
    wa
    #
    @1
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @7
    @11
    wi
    @1
    @2
    @6
    simpll
    @4
    @13
    @3
    @5
    cM
    nn0z
    ad2antrl
    #
    @6
    @14
    @3
    @5
    @14
    @4
    cN
    nn0z
    adantl
    adantl
    #
    cM
    cN
    cV
    cW
    swrdlend
    syl3anc
    3impia
    @3
    @6
    @7
    @10
    c0
    wceq
    #
    @12
    @2
    @13
    @14
    @7
    @17
    wi
    @1
    @2
    @6
    simplr
    @15
    @16
    cM
    cN
    cV
    cU
    swrdlend
    syl3anc
    3impia
    eqtr4d
end
