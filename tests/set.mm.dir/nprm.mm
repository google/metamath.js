include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "wne.mm"
include "cprime.mm"
include "wn.mm"
include "cz.mm"
include "eluzelz.mm"
include "adantr.mm"
include "zred.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cn.mm"
include "eluz2b2.mm"
include "simprbi.mm"
include "adantl.mm"
include "cr.mm"
include "cc0.mm"
include "wb.mm"
include "eluz2nn.mm"
include "nngt0d.mm"
include "ltmulgt11.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "ltned.mm"
include "cdvds.mm"
include "wceq.mm"
include "dvdsmul1.mm"
include "syl2an.mm"
include "wi.mm"
include "cv.mm"
include "wral.mm"
include "isprm4.mm"
include "breq1.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl5.mm"
include "mpid.mm"
include "necon3ad.mm"
include "mpd.mm"

theorem nprm
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ B e. ( ZZ>= ` 2 ) ) -> -. ( A x. B ) e. Prime )

  proof
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cA
    cA
    cB
    cmul
    co
    #
    wne
    @4
    cprime
    wcel
    #
    wn
    @3
    cA
    @4
    @3
    cA
    @1
    cA
    cz
    wcel
    #
    @2
    c2
    cA
    eluzelz
    #
    adantr
    zred
    #
    @3
    c1
    cB
    clt
    wbr
    #
    cA
    @4
    clt
    wbr
    #
    @2
    @9
    @1
    @2
    cB
    cn
    wcel
    @9
    cB
    eluz2b2
    simprbi
    adantl
    @3
    cA
    cr
    wcel
    cB
    cr
    wcel
    cc0
    cA
    clt
    wbr
    @9
    @10
    wb
    @8
    @3
    cB
    @2
    cB
    cz
    wcel
    #
    @1
    c2
    cB
    eluzelz
    #
    adantl
    zred
    @3
    cA
    @1
    cA
    cn
    wcel
    @2
    cA
    eluz2nn
    adantr
    nngt0d
    cA
    cB
    ltmulgt11
    syl3anc
    mpbid
    ltned
    @3
    @5
    cA
    @4
    @3
    @5
    cA
    @4
    cdvds
    wbr
    #
    cA
    @4
    wceq
    #
    @1
    @6
    @11
    @13
    @2
    @7
    @12
    cA
    cB
    dvdsmul1
    syl2an
    @1
    @5
    @13
    @14
    wi
    #
    wi
    @2
    @5
    vx
    cv
    #
    @4
    cdvds
    wbr
    #
    @16
    @4
    wceq
    #
    wi
    #
    vx
    @0
    wral
    #
    @1
    @15
    @5
    @4
    @0
    wcel
    @20
    vx
    @4
    isprm4
    simprbi
    @19
    @15
    vx
    cA
    @0
    @16
    cA
    wceq
    @17
    @13
    @18
    @14
    @16
    cA
    @4
    cdvds
    breq1
    @16
    cA
    @4
    eqeq1
    imbi12d
    rspcv
    syl5
    adantr
    mpid
    necon3ad
    mpd
end
