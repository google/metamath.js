include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "cle.mm"
include "w3a.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wne.mm"
include "wi.mm"
include "c1.mm"
include "cif.mm"
include "breq2.mm"
include "oveq2.mm"
include "neeq1d.mm"
include "imbi12d.mm"
include "breq1.mm"
include "neeq2.mm"
include "oveq1.mm"
include "imbi2d.mm"
include "1z.mm"
include "elimel.mm"
include "1nn.mm"
include "dvdslelem.mm"
include "dedth3h.mm"
include "3expia.mm"
include "com23.mm"
include "3impia.mm"
include "imp.mm"
include "neneqd.mm"
include "nrexdv.mm"
include "wb.mm"
include "nnz.mm"
include "divides.mm"
include "sylan2.mm"
include "3adant3.mm"
include "mtbird.mm"
include "con2d.mm"
include "cr.mm"
include "zre.mm"
include "nnre.mm"
include "lenlt.mm"
include "syl2an.mm"
include "sylibrd.mm"

theorem dvdsle
  let cM: class M
  let cN: class N
  let vn: setvar n


  assert |- ( ( M e. ZZ /\ N e. NN ) -> ( M || N -> M <_ N ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    cM
    cN
    cdvds
    wbr
    #
    cN
    cM
    clt
    wbr
    #
    wn
    #
    cM
    cN
    cle
    wbr
    #
    @2
    @4
    @3
    @0
    @1
    @4
    @3
    wn
    @0
    @1
    @4
    w3a
    #
    @3
    vn
    cv
    #
    cM
    cmul
    co
    #
    cN
    wceq
    #
    vn
    cz
    wrex
    #
    @7
    @10
    vn
    cz
    @7
    @8
    cz
    wcel
    #
    wa
    @9
    cN
    @7
    @12
    @9
    cN
    wne
    #
    @0
    @1
    @4
    @12
    @13
    wi
    @2
    @12
    @4
    @13
    @0
    @1
    @12
    @4
    @13
    wi
    #
    @0
    @1
    @12
    @14
    cN
    @0
    cM
    c1
    cif
    #
    clt
    wbr
    #
    @8
    @15
    cmul
    co
    #
    cN
    wne
    #
    wi
    @1
    cN
    c1
    cif
    #
    @15
    clt
    wbr
    #
    @17
    @19
    wne
    #
    wi
    @20
    @12
    @8
    c1
    cif
    #
    @15
    cmul
    co
    #
    @19
    wne
    #
    wi
    cM
    cN
    @8
    c1
    c1
    c1
    cM
    @15
    wceq
    #
    @4
    @16
    @13
    @18
    cM
    @15
    cN
    clt
    breq2
    @25
    @9
    @17
    cN
    cM
    @15
    @8
    cmul
    oveq2
    neeq1d
    imbi12d
    cN
    @19
    wceq
    @16
    @20
    @18
    @21
    cN
    @19
    @15
    clt
    breq1
    cN
    @19
    @17
    neeq2
    imbi12d
    @8
    @22
    wceq
    #
    @21
    @24
    @20
    @26
    @17
    @23
    @19
    @8
    @22
    @15
    cmul
    oveq1
    neeq1d
    imbi2d
    @22
    @15
    @19
    cM
    c1
    cz
    1z
    elimel
    cN
    c1
    cn
    1nn
    elimel
    @8
    c1
    cz
    1z
    elimel
    dvdslelem
    dedth3h
    3expia
    com23
    3impia
    imp
    neneqd
    nrexdv
    @0
    @1
    @3
    @11
    wb
    #
    @4
    @1
    @0
    cN
    cz
    wcel
    @27
    cN
    nnz
    vn
    cM
    cN
    divides
    sylan2
    3adant3
    mtbird
    3expia
    con2d
    @0
    cM
    cr
    wcel
    cN
    cr
    wcel
    @6
    @5
    wb
    @1
    cM
    zre
    cN
    nnre
    cM
    cN
    lenlt
    syl2an
    sylibrd
end
