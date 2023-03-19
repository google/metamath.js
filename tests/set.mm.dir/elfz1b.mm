include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cn.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "wa.mm"
include "cz.mm"
include "elfz2.mm"
include "simpl2.mm"
include "cr.mm"
include "wi.mm"
include "1red.mm"
include "zre.mm"
include "3ad2ant3.mm"
include "3ad2ant2.mm"
include "letr.mm"
include "syl3anc.mm"
include "imp.mm"
include "elnnz1.mm"
include "sylanbrc.mm"
include "sylbi.mm"
include "elfzel2.mm"
include "fznn.mm"
include "biimpd.mm"
include "mpcom.mm"
include "3anan12.mm"
include "wb.mm"
include "nnz.mm"
include "syl.mm"
include "biimprd.mm"
include "expd.mm"
include "3imp21.mm"
include "impbii.mm"

theorem elfz1b
  let cM: class M
  let cN: class N


  assert |- ( N e. ( 1 ... M ) <-> ( N e. NN /\ M e. NN /\ N <_ M ) )

  proof
    cN
    c1
    cM
    cfz
    co
    wcel
    #
    cN
    cn
    wcel
    #
    cM
    cn
    wcel
    #
    cN
    cM
    cle
    wbr
    #
    w3a
    #
    @0
    @2
    @1
    @3
    wa
    #
    @4
    @0
    c1
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    #
    c1
    cN
    cle
    wbr
    @3
    wa
    #
    wa
    #
    @2
    cN
    c1
    cM
    elfz2
    @11
    @7
    c1
    cM
    cle
    wbr
    #
    @2
    @6
    @7
    @8
    @10
    simpl2
    @9
    @10
    @12
    @9
    c1
    cr
    wcel
    cN
    cr
    wcel
    #
    cM
    cr
    wcel
    #
    @10
    @12
    wi
    @9
    1red
    @8
    @6
    @13
    @7
    cN
    zre
    3ad2ant3
    @7
    @6
    @14
    @8
    cM
    zre
    3ad2ant2
    c1
    cN
    cM
    letr
    syl3anc
    imp
    cM
    elnnz1
    sylanbrc
    sylbi
    @7
    @0
    @5
    cN
    c1
    cM
    elfzel2
    @7
    @0
    @5
    cN
    cM
    fznn
    #
    biimpd
    mpcom
    @1
    @2
    @3
    3anan12
    sylanbrc
    @2
    @1
    @3
    @0
    @2
    @1
    @3
    @0
    @2
    @0
    @5
    @2
    @7
    @0
    @5
    wb
    cM
    nnz
    @15
    syl
    biimprd
    expd
    3imp21
    impbii
end
