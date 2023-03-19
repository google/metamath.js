include "cc0.mm"
include "c1.mm"
include "c2.mm"
include "clog.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cem.mm"
include "cle.mm"
include "ce.mm"
include "ceu.mm"
include "c3.mm"
include "egt2lt3.mm"
include "simpli.mm"
include "crp.mm"
include "wcel.mm"
include "wceq.mm"
include "2rp.mm"
include "reeflog.mm"
include "ax-mp.mm"
include "df-e.mm"
include "eqcomi.mm"
include "3brtr4i.mm"
include "cr.mm"
include "wb.mm"
include "relogcl.mm"
include "1re.mm"
include "eflt.mm"
include "mp2an.mm"
include "mpbir.mm"
include "posdifi.mm"
include "mpbi.mm"
include "cicc.mm"
include "emcl.mm"
include "resubcli.mm"
include "elicc2i.mm"
include "simp2bi.mm"
include "0re.mm"
include "emre.mm"
include "ltletri.mm"

theorem emgt0



  assert |- 0 < gamma

  proof
    cc0
    c1
    c2
    clog
    cfv
    #
    cmin
    co
    #
    clt
    wbr
    #
    @1
    cem
    cle
    wbr
    #
    cc0
    cem
    clt
    wbr
    @0
    c1
    clt
    wbr
    #
    @2
    @4
    @0
    ce
    cfv
    #
    c1
    ce
    cfv
    #
    clt
    wbr
    #
    c2
    ceu
    @5
    @6
    clt
    c2
    ceu
    clt
    wbr
    ceu
    c3
    clt
    wbr
    egt2lt3
    simpli
    c2
    crp
    wcel
    #
    @5
    c2
    wceq
    2rp
    c2
    reeflog
    ax-mp
    ceu
    @6
    df-e
    eqcomi
    3brtr4i
    @0
    cr
    wcel
    #
    c1
    cr
    wcel
    @4
    @7
    wb
    @8
    @9
    2rp
    c2
    relogcl
    ax-mp
    #
    1re
    @0
    c1
    eflt
    mp2an
    mpbir
    @0
    c1
    @10
    1re
    posdifi
    mpbi
    cem
    @1
    c1
    cicc
    co
    wcel
    #
    @3
    emcl
    @11
    cem
    cr
    wcel
    @3
    cem
    c1
    cle
    wbr
    @1
    c1
    cem
    c1
    @0
    1re
    @10
    resubcli
    #
    1re
    elicc2i
    simp2bi
    ax-mp
    cc0
    @1
    cem
    0re
    @12
    emre
    ltletri
    mp2an
end
