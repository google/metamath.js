include "cpi.mm"
include "c4.mm"
include "cdiv.mm"
include "co.mm"
include "ctan.mm"
include "cfv.mm"
include "csin.mm"
include "ccos.mm"
include "c1.mm"
include "c2.mm"
include "csqrt.mm"
include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "cr.mm"
include "cn.mm"
include "pire.mm"
include "4nn.mm"
include "nndivre.mm"
include "mp2an.mm"
include "recni.mm"
include "sincos4thpi.mm"
include "simpri.mm"
include "sqrt2re.mm"
include "cexp.mm"
include "cle.mm"
include "wbr.mm"
include "2re.mm"
include "0le2.mm"
include "resqrtth.mm"
include "2ne0.mm"
include "eqnetri.mm"
include "wb.mm"
include "sqne0.mm"
include "ax-mp.mm"
include "mpbi.mm"
include "recne0.mm"
include "tanval.mm"
include "simpli.mm"
include "oveq12i.mm"
include "reccli.mm"
include "dividi.mm"
include "3eqtri.mm"

theorem tan4thpi



  assert |- ( tan ` ( _pi / 4 ) ) = 1

  proof
    cpi
    c4
    cdiv
    co
    #
    ctan
    cfv
    #
    @0
    csin
    cfv
    #
    @0
    ccos
    cfv
    #
    cdiv
    co
    #
    c1
    c2
    csqrt
    cfv
    #
    cdiv
    co
    #
    @6
    cdiv
    co
    c1
    @0
    cc
    wcel
    @3
    cc0
    wne
    @1
    @4
    wceq
    @0
    cpi
    cr
    wcel
    c4
    cn
    wcel
    @0
    cr
    wcel
    pire
    4nn
    cpi
    c4
    nndivre
    mp2an
    recni
    @3
    @6
    cc0
    @2
    @6
    wceq
    #
    @3
    @6
    wceq
    #
    sincos4thpi
    simpri
    #
    @5
    cc
    wcel
    #
    @5
    cc0
    wne
    #
    @6
    cc0
    wne
    @5
    sqrt2re
    recni
    #
    @5
    c2
    cexp
    co
    #
    cc0
    wne
    #
    @11
    @13
    c2
    cc0
    c2
    cr
    wcel
    cc0
    c2
    cle
    wbr
    @13
    c2
    wceq
    2re
    0le2
    c2
    resqrtth
    mp2an
    2ne0
    eqnetri
    @10
    @14
    @11
    wb
    @12
    @5
    sqne0
    ax-mp
    mpbi
    #
    @5
    recne0
    mp2an
    #
    eqnetri
    @0
    tanval
    mp2an
    @2
    @6
    @3
    @6
    cdiv
    @7
    @8
    sincos4thpi
    simpli
    @9
    oveq12i
    @6
    @5
    @12
    @15
    reccli
    @16
    dividi
    3eqtri
end
