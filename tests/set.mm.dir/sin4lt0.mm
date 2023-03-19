include "c4.mm"
include "csin.mm"
include "cfv.mm"
include "c2.mm"
include "ccos.mm"
include "cmul.mm"
include "co.mm"
include "cc0.mm"
include "clt.mm"
include "2t2e4.mm"
include "fveq2i.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "2cn.mm"
include "sin2t.mm"
include "ax-mp.mm"
include "eqtr3i.mm"
include "wbr.mm"
include "sincos2sgn.mm"
include "simpri.mm"
include "cr.mm"
include "wa.mm"
include "wb.mm"
include "2re.mm"
include "recoscl.mm"
include "0re.mm"
include "resincl.mm"
include "simpli.mm"
include "pm3.2i.mm"
include "ltmul2.mm"
include "mp3an.mm"
include "mpbi.mm"
include "recni.mm"
include "mul01i.mm"
include "breqtri.mm"
include "remulcli.mm"
include "2pos.mm"
include "eqbrtri.mm"

theorem sin4lt0



  assert |- ( sin ` 4 ) < 0

  proof
    c4
    csin
    cfv
    #
    c2
    c2
    csin
    cfv
    #
    c2
    ccos
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    cc0
    clt
    c2
    c2
    cmul
    co
    #
    csin
    cfv
    #
    @0
    @4
    @5
    c4
    csin
    2t2e4
    fveq2i
    c2
    cc
    wcel
    @6
    @4
    wceq
    2cn
    c2
    sin2t
    ax-mp
    eqtr3i
    @4
    c2
    cc0
    cmul
    co
    #
    cc0
    clt
    @3
    cc0
    clt
    wbr
    #
    @4
    @7
    clt
    wbr
    #
    @3
    @1
    cc0
    cmul
    co
    #
    cc0
    clt
    @2
    cc0
    clt
    wbr
    #
    @3
    @10
    clt
    wbr
    #
    cc0
    @1
    clt
    wbr
    #
    @11
    sincos2sgn
    simpri
    @2
    cr
    wcel
    #
    cc0
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    @13
    wa
    @11
    @12
    wb
    c2
    cr
    wcel
    #
    @14
    2re
    c2
    recoscl
    ax-mp
    #
    0re
    @16
    @13
    @17
    @16
    2re
    c2
    resincl
    ax-mp
    #
    @13
    @11
    sincos2sgn
    simpli
    pm3.2i
    @2
    cc0
    @1
    ltmul2
    mp3an
    mpbi
    @1
    @1
    @19
    recni
    mul01i
    breqtri
    @3
    cr
    wcel
    @15
    @17
    cc0
    c2
    clt
    wbr
    #
    wa
    @8
    @9
    wb
    @1
    @2
    @19
    @18
    remulcli
    0re
    @17
    @20
    2re
    2pos
    pm3.2i
    @3
    cc0
    c2
    ltmul2
    mp3an
    mpbi
    c2
    2cn
    mul01i
    breqtri
    eqbrtri
end
