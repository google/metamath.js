include "cword.mm"
include "wcel.mm"
include "cn.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "cfzo.mm"
include "lbfzo0.mm"
include "ne0i.mm"
include "sylbir.mm"
include "3ad2ant2.mm"
include "wf.mm"
include "wceq.mm"
include "wb.mm"
include "cfz.mm"
include "simp1.mm"
include "cn0.mm"
include "nnnn0.mm"
include "lencl.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "swrd0f.mm"
include "syl2anc.mm"
include "f0dom0.mm"
include "bicomd.mm"
include "syl.mm"
include "necon3bid.mm"
include "mpbird.mm"

theorem swrdn0
  let cN: class N
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ N e. NN /\ N <_ ( # ` W ) ) -> ( W substr <. 0 , N >. ) =/= (/) )

  proof
    cW
    cV
    cword
    wcel
    #
    cN
    cn
    wcel
    #
    cN
    cW
    chash
    cfv
    #
    cle
    wbr
    #
    w3a
    #
    cW
    cc0
    cN
    cop
    csubstr
    co
    #
    c0
    wne
    cc0
    cN
    cfzo
    co
    #
    c0
    wne
    #
    @1
    @0
    @7
    @3
    @1
    cc0
    @6
    wcel
    @7
    cN
    lbfzo0
    @6
    cc0
    ne0i
    sylbir
    3ad2ant2
    @4
    @5
    c0
    @6
    c0
    @4
    @6
    cV
    @5
    wf
    #
    @5
    c0
    wceq
    #
    @6
    c0
    wceq
    #
    wb
    @4
    @0
    cN
    cc0
    @2
    cfz
    co
    wcel
    #
    @8
    @0
    @1
    @3
    simp1
    @4
    cN
    cn0
    wcel
    #
    @2
    cn0
    wcel
    #
    @3
    @11
    @1
    @0
    @12
    @3
    cN
    nnnn0
    3ad2ant2
    @0
    @1
    @13
    @3
    cV
    cW
    lencl
    3ad2ant1
    @0
    @1
    @3
    simp3
    cN
    @2
    elfz2nn0
    syl3anbrc
    cN
    cV
    cW
    swrd0f
    syl2anc
    @8
    @10
    @9
    @5
    @6
    cV
    f0dom0
    bicomd
    syl
    necon3bid
    mpbird
end
