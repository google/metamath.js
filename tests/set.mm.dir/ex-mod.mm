include "c5.mm"
include "c3.mm"
include "cmo.mm"
include "co.mm"
include "c2.mm"
include "wceq.mm"
include "c7.mm"
include "cneg.mm"
include "c1.mm"
include "caddc.mm"
include "3p2e5.mm"
include "eqcomi.mm"
include "oveq1i.mm"
include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "2nn0.mm"
include "3nn.mm"
include "2lt3.mm"
include "addmodid.mm"
include "mp3an.mm"
include "eqtri.mm"
include "cdvds.mm"
include "wn.mm"
include "2re.mm"
include "2lt7.mm"
include "ltneii.mm"
include "cuz.mm"
include "cfv.mm"
include "cprime.mm"
include "wb.mm"
include "wa.mm"
include "2nn.mm"
include "1lt2.mm"
include "pm3.2i.mm"
include "eluz2b2.mm"
include "mpbir.mm"
include "7prm.mm"
include "dvdsprm.mm"
include "mp2an.mm"
include "nemtbir.mm"
include "cz.mm"
include "2z.mm"
include "7nn.mm"
include "nnzi.mm"
include "dvdsnegb.mm"
include "mtbi.mm"
include "znegcl.mm"
include "mod2eq1n2dvds.mm"
include "mp2b.mm"

theorem ex-mod



  assert |- ( ( 5 mod 3 ) = 2 /\ ( -u 7 mod 2 ) = 1 )

  proof
    c5
    c3
    cmo
    co
    #
    c2
    wceq
    c7
    cneg
    #
    c2
    cmo
    co
    c1
    wceq
    #
    @0
    c3
    c2
    caddc
    co
    #
    c3
    cmo
    co
    #
    c2
    c5
    @3
    c3
    cmo
    @3
    c5
    3p2e5
    eqcomi
    oveq1i
    c2
    cn0
    wcel
    c3
    cn
    wcel
    c2
    c3
    clt
    wbr
    @4
    c2
    wceq
    2nn0
    3nn
    2lt3
    c2
    c3
    addmodid
    mp3an
    eqtri
    @2
    c2
    @1
    cdvds
    wbr
    #
    wn
    #
    c2
    c7
    cdvds
    wbr
    #
    @5
    @7
    c2
    c7
    c2
    c7
    2re
    2lt7
    ltneii
    c2
    c2
    cuz
    cfv
    wcel
    #
    c7
    cprime
    wcel
    @7
    c2
    c7
    wceq
    wb
    @8
    c2
    cn
    wcel
    #
    c1
    c2
    clt
    wbr
    #
    wa
    @9
    @10
    2nn
    1lt2
    pm3.2i
    c2
    eluz2b2
    mpbir
    7prm
    c7
    c2
    dvdsprm
    mp2an
    nemtbir
    c2
    cz
    wcel
    c7
    cz
    wcel
    #
    @7
    @5
    wb
    2z
    c7
    7nn
    nnzi
    #
    c2
    c7
    dvdsnegb
    mp2an
    mtbi
    @11
    @1
    cz
    wcel
    @2
    @6
    wb
    @12
    c7
    znegcl
    @1
    mod2eq1n2dvds
    mp2b
    mpbir
    pm3.2i
end
