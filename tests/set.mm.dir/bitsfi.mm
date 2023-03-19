include "cn0.mm"
include "wcel.mm"
include "c2.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cbits.mm"
include "cfv.mm"
include "cfn.mm"
include "cn.mm"
include "cr.mm"
include "c1.mm"
include "wrex.mm"
include "nn0re.mm"
include "2re.mm"
include "a1i.mm"
include "1lt2.mm"
include "expnbnd.mm"
include "syl3anc.mm"
include "wa.mm"
include "cc0.mm"
include "cfzo.mm"
include "wss.mm"
include "fzofi.mm"
include "cuz.mm"
include "cz.mm"
include "simpl.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "2nn.mm"
include "simprl.mm"
include "nnnn0d.mm"
include "nnexpcld.mm"
include "nnzd.mm"
include "simprr.mm"
include "elfzo2.mm"
include "syl3anbrc.mm"
include "wb.mm"
include "nn0zd.mm"
include "bitsfzo.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "ssfi.mm"
include "sylancr.mm"
include "rexlimddv.mm"

theorem bitsfi
  let cN: class N
  let vm: setvar m
  let vx: setvar x
  let cM: class M
  let vn: setvar n


  assert |- ( N e. NN0 -> ( bits ` N ) e. Fin )

  proof
    cN
    cn0
    wcel
    #
    cN
    c2
    vm
    cv
    #
    cexp
    co
    #
    clt
    wbr
    #
    cN
    cbits
    cfv
    #
    cfn
    wcel
    #
    vm
    cn
    @0
    cN
    cr
    wcel
    c2
    cr
    wcel
    #
    c1
    c2
    clt
    wbr
    #
    @3
    vm
    cn
    wrex
    cN
    nn0re
    @6
    @0
    2re
    a1i
    @7
    @0
    1lt2
    a1i
    cN
    c2
    vm
    expnbnd
    syl3anc
    @0
    @1
    cn
    wcel
    #
    @3
    wa
    #
    wa
    #
    cc0
    @1
    cfzo
    co
    #
    cfn
    wcel
    @4
    @11
    wss
    #
    @5
    cc0
    @1
    fzofi
    @10
    cN
    cc0
    @2
    cfzo
    co
    wcel
    #
    @12
    @10
    cN
    cc0
    cuz
    cfv
    #
    wcel
    @2
    cz
    wcel
    @3
    @13
    @10
    cN
    cn0
    @14
    @0
    @9
    simpl
    #
    nn0uz
    syl6eleq
    @10
    @2
    @10
    c2
    @1
    c2
    cn
    wcel
    @10
    2nn
    a1i
    @10
    @1
    @0
    @8
    @3
    simprl
    nnnn0d
    #
    nnexpcld
    nnzd
    @0
    @8
    @3
    simprr
    cN
    cc0
    @2
    elfzo2
    syl3anbrc
    @10
    cN
    cz
    wcel
    @1
    cn0
    wcel
    @13
    @12
    wb
    @10
    cN
    @15
    nn0zd
    @16
    @1
    cN
    bitsfzo
    syl2anc
    mpbid
    @11
    @4
    ssfi
    sylancr
    rexlimddv
end
