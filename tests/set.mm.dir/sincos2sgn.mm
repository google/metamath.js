include "cc0.mm"
include "c2.mm"
include "csin.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "ccos.mm"
include "cioc.mm"
include "co.mm"
include "wcel.mm"
include "cr.mm"
include "cle.mm"
include "2re.mm"
include "2pos.mm"
include "leidi.mm"
include "cxr.mm"
include "w3a.mm"
include "wb.mm"
include "0xr.mm"
include "elioc2.mm"
include "mp2an.mm"
include "mpbir3an.mm"
include "sin02gt0.mm"
include "ax-mp.mm"
include "c1.mm"
include "c9.mm"
include "cdiv.mm"
include "cneg.mm"
include "c7.mm"
include "cos2bnd.mm"
include "simpri.mm"
include "9re.mm"
include "9pos.mm"
include "recgt0ii.mm"
include "gt0ne0ii.mm"
include "rereccli.mm"
include "lt0neg2.mm"
include "mpbi.mm"
include "recoscl.mm"
include "renegcli.mm"
include "0re.mm"
include "lttri.mm"
include "pm3.2i.mm"

theorem sincos2sgn



  assert |- ( 0 < ( sin ` 2 ) /\ ( cos ` 2 ) < 0 )

  proof
    cc0
    c2
    csin
    cfv
    clt
    wbr
    #
    c2
    ccos
    cfv
    #
    cc0
    clt
    wbr
    #
    c2
    cc0
    c2
    cioc
    co
    wcel
    #
    @0
    @3
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    c2
    c2
    cle
    wbr
    #
    2re
    2pos
    c2
    2re
    leidi
    cc0
    cxr
    wcel
    @4
    @3
    @4
    @5
    @6
    w3a
    wb
    0xr
    2re
    cc0
    c2
    c2
    elioc2
    mp2an
    mpbir3an
    c2
    sin02gt0
    ax-mp
    @1
    c1
    c9
    cdiv
    co
    #
    cneg
    #
    clt
    wbr
    #
    @8
    cc0
    clt
    wbr
    #
    @2
    c7
    c9
    cdiv
    co
    cneg
    @1
    clt
    wbr
    @9
    cos2bnd
    simpri
    cc0
    @7
    clt
    wbr
    #
    @10
    c9
    9re
    9pos
    recgt0ii
    @7
    cr
    wcel
    @11
    @10
    wb
    c9
    9re
    c9
    9re
    9pos
    gt0ne0ii
    rereccli
    #
    @7
    lt0neg2
    ax-mp
    mpbi
    @1
    @8
    cc0
    @4
    @1
    cr
    wcel
    2re
    c2
    recoscl
    ax-mp
    @7
    @12
    renegcli
    0re
    lttri
    mp2an
    pm3.2i
end
