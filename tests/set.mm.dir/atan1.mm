include "cpi.mm"
include "c4.mm"
include "cdiv.mm"
include "co.mm"
include "ctan.mm"
include "cfv.mm"
include "catan.mm"
include "c1.mm"
include "tan4thpi.mm"
include "fveq2i.mm"
include "cc.mm"
include "wcel.mm"
include "cre.mm"
include "c2.mm"
include "cneg.mm"
include "cioo.mm"
include "wceq.mm"
include "cr.mm"
include "cn.mm"
include "pire.mm"
include "4nn.mm"
include "nndivre.mm"
include "mp2an.mm"
include "recni.mm"
include "rere.mm"
include "ax-mp.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "crp.mm"
include "pirp.mm"
include "rphalfcl.mm"
include "rpgt0.mm"
include "wb.mm"
include "halfpire.mm"
include "lt0neg2.mm"
include "mpbi.mm"
include "nnrp.mm"
include "rpdivcl.mm"
include "neghalfpire.mm"
include "0re.mm"
include "lttri.mm"
include "cmul.mm"
include "wne.mm"
include "wa.mm"
include "2cnne0.mm"
include "divdiv1.mm"
include "mp3an.mm"
include "2t2e4.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "rphalflt.mm"
include "eqbrtrri.mm"
include "cxr.mm"
include "w3a.mm"
include "rexri.mm"
include "elioo2.mm"
include "mpbir3an.mm"
include "eqeltri.mm"
include "atantan.mm"
include "eqtr3i.mm"

theorem atan1



  assert |- ( arctan ` 1 ) = ( _pi / 4 )

  proof
    cpi
    c4
    cdiv
    co
    #
    ctan
    cfv
    #
    catan
    cfv
    #
    c1
    catan
    cfv
    @0
    @1
    c1
    catan
    tan4thpi
    fveq2i
    @0
    cc
    wcel
    @0
    cre
    cfv
    #
    cpi
    c2
    cdiv
    co
    #
    cneg
    #
    @4
    cioo
    co
    #
    wcel
    @2
    @0
    wceq
    @0
    cpi
    cr
    wcel
    c4
    cn
    wcel
    #
    @0
    cr
    wcel
    #
    pire
    4nn
    cpi
    c4
    nndivre
    mp2an
    #
    recni
    @3
    @0
    @6
    @8
    @3
    @0
    wceq
    @9
    @0
    rere
    ax-mp
    @0
    @6
    wcel
    #
    @8
    @5
    @0
    clt
    wbr
    #
    @0
    @4
    clt
    wbr
    #
    @9
    @5
    cc0
    clt
    wbr
    #
    cc0
    @0
    clt
    wbr
    #
    @11
    cc0
    @4
    clt
    wbr
    #
    @13
    @4
    crp
    wcel
    #
    @15
    cpi
    crp
    wcel
    #
    @16
    pirp
    cpi
    rphalfcl
    ax-mp
    #
    @4
    rpgt0
    ax-mp
    @4
    cr
    wcel
    @15
    @13
    wb
    halfpire
    @4
    lt0neg2
    ax-mp
    mpbi
    @0
    crp
    wcel
    #
    @14
    @17
    c4
    crp
    wcel
    #
    @19
    pirp
    @7
    @20
    4nn
    c4
    nnrp
    ax-mp
    cpi
    c4
    rpdivcl
    mp2an
    @0
    rpgt0
    ax-mp
    @5
    cc0
    @0
    neghalfpire
    0re
    @9
    lttri
    mp2an
    @4
    c2
    cdiv
    co
    #
    @0
    @4
    clt
    @21
    cpi
    c2
    c2
    cmul
    co
    #
    cdiv
    co
    #
    @0
    cpi
    cc
    wcel
    c2
    cc
    wcel
    c2
    cc0
    wne
    wa
    #
    @24
    @21
    @23
    wceq
    cpi
    pire
    recni
    2cnne0
    2cnne0
    cpi
    c2
    c2
    divdiv1
    mp3an
    @22
    c4
    cpi
    cdiv
    2t2e4
    oveq2i
    eqtri
    @16
    @21
    @4
    clt
    wbr
    @18
    @4
    rphalflt
    ax-mp
    eqbrtrri
    @5
    cxr
    wcel
    @4
    cxr
    wcel
    @10
    @8
    @11
    @12
    w3a
    wb
    @5
    neghalfpire
    rexri
    @4
    halfpire
    rexri
    @5
    @4
    @0
    elioo2
    mp2an
    mpbir3an
    eqeltri
    @0
    atantan
    mp2an
    eqtr3i
end
