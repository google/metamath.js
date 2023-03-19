include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cdvds.mm"
include "wbr.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cmul.mm"
include "cmin.mm"
include "cc0.mm"
include "cr.mm"
include "crp.mm"
include "wceq.mm"
include "simpl3.mm"
include "zred.mm"
include "simpl2.mm"
include "nnrpd.mm"
include "modval.mm"
include "syl2anc.mm"
include "breq2d.mm"
include "simpl1.mm"
include "nnzd.mm"
include "nndivred.mm"
include "flcld.mm"
include "simpr.mm"
include "dvdsmultr1d.mm"
include "zmulcld.mm"
include "zcnd.mm"
include "subid1d.mm"
include "breqtrrd.mm"
include "wb.mm"
include "0zd.mm"
include "moddvds.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "eqeq2d.mm"
include "3bitr3d.mm"
include "3bitrd.mm"

theorem dvdsmod
  let cP: class P
  let cK: class K
  let cN: class N


  assert |- ( ( ( P e. NN /\ N e. NN /\ K e. ZZ ) /\ P || N ) -> ( P || ( K mod N ) <-> P || K ) )

  proof
    cP
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    cK
    cz
    wcel
    #
    w3a
    #
    cP
    cN
    cdvds
    wbr
    #
    wa
    #
    cP
    cK
    cN
    cmo
    co
    #
    cdvds
    wbr
    cP
    cK
    cN
    cK
    cN
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    cdvds
    wbr
    #
    cP
    cK
    cc0
    cmin
    co
    #
    cdvds
    wbr
    #
    cP
    cK
    cdvds
    wbr
    @5
    @6
    @10
    cP
    cdvds
    @5
    cK
    cr
    wcel
    cN
    crp
    wcel
    @6
    @10
    wceq
    @5
    cK
    @0
    @1
    @2
    @4
    simpl3
    #
    zred
    #
    @5
    cN
    @0
    @1
    @2
    @4
    simpl2
    #
    nnrpd
    cK
    cN
    modval
    syl2anc
    breq2d
    @5
    cK
    cP
    cmo
    co
    #
    @9
    cP
    cmo
    co
    #
    wceq
    #
    @17
    cc0
    cP
    cmo
    co
    #
    wceq
    #
    @11
    @13
    @5
    @18
    @20
    @17
    @5
    @18
    @20
    wceq
    #
    cP
    @9
    cc0
    cmin
    co
    #
    cdvds
    wbr
    #
    @5
    cP
    @9
    @23
    cdvds
    @5
    cP
    cN
    @8
    @5
    cP
    @0
    @1
    @2
    @4
    simpl1
    #
    nnzd
    @5
    cN
    @16
    nnzd
    #
    @5
    @7
    @5
    cK
    cN
    @15
    @16
    nndivred
    flcld
    #
    @3
    @4
    simpr
    dvdsmultr1d
    @5
    @9
    @5
    @9
    @5
    cN
    @8
    @26
    @27
    zmulcld
    #
    zcnd
    subid1d
    breqtrrd
    @5
    @0
    @9
    cz
    wcel
    #
    cc0
    cz
    wcel
    #
    @22
    @24
    wb
    @25
    @28
    @5
    0zd
    #
    @9
    cc0
    cP
    moddvds
    syl3anc
    mpbird
    eqeq2d
    @5
    @0
    @2
    @29
    @19
    @11
    wb
    @25
    @14
    @28
    cK
    @9
    cP
    moddvds
    syl3anc
    @5
    @0
    @2
    @30
    @21
    @13
    wb
    @25
    @14
    @31
    cK
    cc0
    cP
    moddvds
    syl3anc
    3bitr3d
    @5
    @12
    cK
    cP
    cdvds
    @5
    cK
    @5
    cK
    @14
    zcnd
    subid1d
    breq2d
    3bitrd
end
