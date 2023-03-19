include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "c2o.mm"
include "cen.mm"
include "cpr.mm"
include "wceq.mm"
include "simplr.mm"
include "necomd.mm"
include "wi.mm"
include "simpr.mm"
include "cz.mm"
include "nnz.mm"
include "1dvds.mm"
include "syl.mm"
include "ad2antrr.mm"
include "wb.mm"
include "1nn.mm"
include "breq1.mm"
include "elrab3.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "iddvds.mm"
include "mpbird.mm"
include "en2eqpr.mm"
include "syl3anc.mm"
include "mpd.mm"
include "ex.mm"
include "necom.mm"
include "pr2ne.mm"
include "mpan.mm"
include "biimpar.mm"
include "sylan2br.mm"
include "syl5ibrcom.mm"
include "impbid.mm"

theorem isprm2lem
  let cP: class P
  let vn: setvar n
  let vz: setvar z

  disjoint P n
  disjoint n z
  disjoint P z
  assert |- ( ( P e. NN /\ P =/= 1 ) -> ( { n e. NN | n || P } ~~ 2o <-> { n e. NN | n || P } = { 1 , P } ) )

  proof
    cP
    cn
    wcel
    #
    cP
    c1
    wne
    #
    wa
    #
    vn
    cv
    #
    cP
    cdvds
    wbr
    #
    vn
    cn
    crab
    #
    c2o
    cen
    wbr
    #
    @5
    c1
    cP
    cpr
    #
    wceq
    #
    @2
    @6
    @8
    @2
    @6
    wa
    #
    c1
    cP
    wne
    #
    @8
    @9
    cP
    c1
    @0
    @1
    @6
    simplr
    necomd
    @9
    @6
    c1
    @5
    wcel
    #
    cP
    @5
    wcel
    #
    @10
    @8
    wi
    @2
    @6
    simpr
    @9
    c1
    cP
    cdvds
    wbr
    #
    @11
    @0
    @13
    @1
    @6
    @0
    cP
    cz
    wcel
    #
    @13
    cP
    nnz
    #
    cP
    1dvds
    syl
    ad2antrr
    c1
    cn
    wcel
    #
    @11
    @13
    wb
    1nn
    @4
    @13
    vn
    c1
    cn
    @3
    c1
    cP
    cdvds
    breq1
    elrab3
    ax-mp
    sylibr
    @9
    @12
    cP
    cP
    cdvds
    wbr
    #
    @0
    @17
    @1
    @6
    @0
    @14
    @17
    @15
    cP
    iddvds
    syl
    ad2antrr
    @0
    @12
    @17
    wb
    @1
    @6
    @4
    @17
    vn
    cP
    cn
    @3
    cP
    cP
    cdvds
    breq1
    elrab3
    ad2antrr
    mpbird
    c1
    cP
    @5
    en2eqpr
    syl3anc
    mpd
    ex
    @2
    @6
    @8
    @7
    c2o
    cen
    wbr
    #
    @1
    @0
    @10
    @18
    c1
    cP
    necom
    @0
    @18
    @10
    @16
    @0
    @18
    @10
    wb
    1nn
    c1
    cP
    cn
    cn
    pr2ne
    mpan
    biimpar
    sylan2br
    @5
    @7
    c2o
    cen
    breq1
    syl5ibrcom
    impbid
end
