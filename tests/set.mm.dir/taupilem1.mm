include "crp.mm"
include "wcel.mm"
include "ccos.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cdiv.mm"
include "cr.mm"
include "2rp.mm"
include "pirp.mm"
include "rpmulcl.mm"
include "mp2an.mm"
include "rpre.mm"
include "ax-mp.mm"
include "recni.mm"
include "cc0.mm"
include "clt.mm"
include "rpgt0.mm"
include "gt0ne0ii.mm"
include "dividi.mm"
include "rpdivcl.mm"
include "rpgt0d.mm"
include "mpan2.mm"
include "adantr.mm"
include "cz.mm"
include "wb.mm"
include "cc.mm"
include "rpcn.mm"
include "coseq1.mm"
include "syl.mm"
include "biimpa.mm"
include "zgt0ge1.mm"
include "mpbid.mm"
include "syl5eqbr.mm"
include "pm3.2i.mm"
include "lediv1.mm"
include "mp3an13.mm"
include "mpbird.mm"

theorem taupilem1
  let cA: class A


  assert |- ( ( A e. RR+ /\ ( cos ` A ) = 1 ) -> ( 2 x. _pi ) <_ A )

  proof
    cA
    crp
    wcel
    #
    cA
    ccos
    cfv
    c1
    wceq
    #
    wa
    #
    c2
    cpi
    cmul
    co
    #
    cA
    cle
    wbr
    #
    @3
    @3
    cdiv
    co
    #
    cA
    @3
    cdiv
    co
    #
    cle
    wbr
    #
    @2
    @5
    c1
    @6
    cle
    @3
    @3
    @3
    crp
    wcel
    #
    @3
    cr
    wcel
    #
    c2
    crp
    wcel
    cpi
    crp
    wcel
    @8
    2rp
    pirp
    c2
    cpi
    rpmulcl
    mp2an
    #
    @3
    rpre
    ax-mp
    #
    recni
    @3
    @11
    @8
    cc0
    @3
    clt
    wbr
    #
    @10
    @3
    rpgt0
    ax-mp
    #
    gt0ne0ii
    dividi
    @2
    cc0
    @6
    clt
    wbr
    #
    c1
    @6
    cle
    wbr
    #
    @0
    @14
    @1
    @0
    @8
    @14
    @10
    @0
    @8
    wa
    @6
    cA
    @3
    rpdivcl
    rpgt0d
    mpan2
    adantr
    @2
    @6
    cz
    wcel
    #
    @14
    @15
    wb
    @0
    @1
    @16
    @0
    cA
    cc
    wcel
    @1
    @16
    wb
    cA
    rpcn
    cA
    coseq1
    syl
    biimpa
    @6
    zgt0ge1
    syl
    mpbid
    syl5eqbr
    @2
    cA
    cr
    wcel
    #
    @4
    @7
    wb
    #
    @0
    @17
    @1
    cA
    rpre
    adantr
    @9
    @17
    @9
    @12
    wa
    @18
    @11
    @9
    @12
    @11
    @13
    pm3.2i
    @3
    cA
    @3
    lediv1
    mp3an13
    syl
    mpbird
end
