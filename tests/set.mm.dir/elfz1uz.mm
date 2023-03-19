include "cn.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "wa.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "simpl.mm"
include "eluzle.mm"
include "adantl.mm"
include "cz.mm"
include "wb.mm"
include "eluzelz.mm"
include "fznn.mm"
include "syl.mm"
include "mpbir2and.mm"

theorem elfz1uz
  let cM: class M
  let cN: class N


  assert |- ( ( N e. NN /\ M e. ( ZZ>= ` N ) ) -> N e. ( 1 ... M ) )

  proof
    cN
    cn
    wcel
    #
    cM
    cN
    cuz
    cfv
    wcel
    #
    wa
    #
    cN
    c1
    cM
    cfz
    co
    wcel
    #
    @0
    cN
    cM
    cle
    wbr
    #
    @0
    @1
    simpl
    @1
    @4
    @0
    cN
    cM
    eluzle
    adantl
    @2
    cM
    cz
    wcel
    #
    @3
    @0
    @4
    wa
    wb
    @1
    @5
    @0
    cN
    cM
    eluzelz
    adantl
    cN
    cM
    fznn
    syl
    mpbir2and
end
