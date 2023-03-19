include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "wa.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "1red.mm"
include "cr.mm"
include "elfzelz.mm"
include "zred.mm"
include "adantl.mm"
include "peano2re.mm"
include "syl.mm"
include "ltp1d.mm"
include "elfzle1.mm"
include "wb.mm"
include "1re.mm"
include "leadd1.mm"
include "mp3an13.mm"
include "mpbid.mm"
include "ltletrd.mm"
include "ltled.mm"
include "elfzle2.mm"
include "cz.mm"
include "nnz.mm"
include "adantr.mm"
include "leaddsub.mm"
include "mp3an2.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "peano2zd.mm"
include "1z.mm"
include "elfz.mm"
include "mpbir2and.mm"

theorem fznatpl1
  let cI: class I
  let cN: class N


  assert |- ( ( N e. NN /\ I e. ( 1 ... ( N - 1 ) ) ) -> ( I + 1 ) e. ( 1 ... N ) )

  proof
    cN
    cn
    wcel
    #
    cI
    c1
    cN
    c1
    cmin
    co
    #
    cfz
    co
    wcel
    #
    wa
    #
    cI
    c1
    caddc
    co
    #
    c1
    cN
    cfz
    co
    wcel
    #
    c1
    @4
    cle
    wbr
    #
    @4
    cN
    cle
    wbr
    #
    @3
    c1
    @4
    @3
    1red
    #
    @3
    cI
    cr
    wcel
    #
    @4
    cr
    wcel
    @2
    @9
    @0
    @2
    cI
    cI
    c1
    @1
    elfzelz
    #
    zred
    adantl
    #
    cI
    peano2re
    syl
    #
    @3
    c1
    c1
    c1
    caddc
    co
    #
    @4
    @8
    @3
    c1
    cr
    wcel
    #
    @13
    cr
    wcel
    @8
    c1
    peano2re
    syl
    @12
    @3
    c1
    @8
    ltp1d
    @3
    c1
    cI
    cle
    wbr
    #
    @13
    @4
    cle
    wbr
    #
    @2
    @15
    @0
    cI
    c1
    @1
    elfzle1
    adantl
    @3
    @9
    @15
    @16
    wb
    #
    @11
    @14
    @9
    @14
    @17
    1re
    1re
    c1
    cI
    c1
    leadd1
    mp3an13
    syl
    mpbid
    ltletrd
    ltled
    @3
    @7
    cI
    @1
    cle
    wbr
    #
    @2
    @18
    @0
    cI
    c1
    @1
    elfzle2
    adantl
    @3
    @9
    cN
    cr
    wcel
    #
    @7
    @18
    wb
    #
    @11
    @3
    cN
    @0
    cN
    cz
    wcel
    #
    @2
    cN
    nnz
    adantr
    #
    zred
    @9
    @14
    @19
    @20
    1re
    cI
    c1
    cN
    leaddsub
    mp3an2
    syl2anc
    mpbird
    @3
    @4
    cz
    wcel
    #
    @21
    @5
    @6
    @7
    wa
    wb
    #
    @2
    @23
    @0
    @2
    cI
    @10
    peano2zd
    adantl
    @22
    @23
    c1
    cz
    wcel
    @21
    @24
    1z
    @4
    c1
    cN
    elfz
    mp3an2
    syl2anc
    mpbir2and
end
