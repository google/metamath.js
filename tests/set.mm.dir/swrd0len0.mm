include "cword.mm"
include "wcel.mm"
include "cn0.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "cc0.mm"
include "cfz.mm"
include "cop.mm"
include "csubstr.mm"
include "simp1.mm"
include "nn0fz0.mm"
include "biimpi.mm"
include "wi.mm"
include "1nn0.mm"
include "elfz0add.mm"
include "mpan2.mm"
include "mpd.mm"
include "3ad2ant2.mm"
include "wb.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "3ad2ant3.mm"
include "mpbird.mm"
include "swrd0len.mm"
include "syl2anc.mm"

theorem swrd0len0
  let cN: class N
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ N e. NN0 /\ ( # ` W ) = ( N + 1 ) ) -> ( # ` ( W substr <. 0 , N >. ) ) = N )

  proof
    cW
    cV
    cword
    wcel
    #
    cN
    cn0
    wcel
    #
    cW
    chash
    cfv
    #
    cN
    c1
    caddc
    co
    #
    wceq
    #
    w3a
    #
    @0
    cN
    cc0
    @2
    cfz
    co
    #
    wcel
    #
    cW
    cc0
    cN
    cop
    csubstr
    co
    chash
    cfv
    cN
    wceq
    @0
    @1
    @4
    simp1
    @5
    @7
    cN
    cc0
    @3
    cfz
    co
    #
    wcel
    #
    @1
    @0
    @9
    @4
    @1
    cN
    cc0
    cN
    cfz
    co
    wcel
    #
    @9
    @1
    @10
    cN
    nn0fz0
    biimpi
    @1
    c1
    cn0
    wcel
    @10
    @9
    wi
    1nn0
    cN
    c1
    cN
    elfz0add
    mpan2
    mpd
    3ad2ant2
    @4
    @0
    @7
    @9
    wb
    @1
    @4
    @6
    @8
    cN
    @2
    @3
    cc0
    cfz
    oveq2
    eleq2d
    3ad2ant3
    mpbird
    cV
    cW
    cN
    swrd0len
    syl2anc
end
