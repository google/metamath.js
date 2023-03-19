include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "csupp.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "ccom.mm"
include "wi.mm"
include "ccnv.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "simpl.mm"
include "anim2i.mm"
include "ancomd.mm"
include "suppimacnv.mm"
include "syl.mm"
include "eqeq1d.mm"
include "coexg.mm"
include "cnvco.mm"
include "imaeq1i.mm"
include "imaco.mm"
include "eqtri.mm"
include "imaeq2.mm"
include "ima0.mm"
include "syl6eq.mm"
include "syl5eq.mm"
include "sylan9eq.mm"
include "ex.mm"
include "sylbid.mm"
include "wn.mm"
include "id.mm"
include "intnand.mm"
include "supp0prc.mm"
include "2a1d.mm"
include "pm2.61i.mm"

theorem supp0cosupp0
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let cZ: class Z


  assert |- ( ( F e. V /\ G e. W ) -> ( ( F supp Z ) = (/) -> ( ( F o. G ) supp Z ) = (/) ) )

  proof
    cZ
    cvv
    wcel
    #
    cF
    cV
    wcel
    #
    cG
    cW
    wcel
    #
    wa
    #
    cF
    cZ
    csupp
    co
    #
    c0
    wceq
    #
    cF
    cG
    ccom
    #
    cZ
    csupp
    co
    #
    c0
    wceq
    #
    wi
    #
    wi
    @0
    @3
    @9
    @0
    @3
    wa
    #
    @5
    cF
    ccnv
    #
    cvv
    cZ
    csn
    cdif
    #
    cima
    #
    c0
    wceq
    #
    @8
    @10
    @4
    @13
    c0
    @10
    @1
    @0
    wa
    @4
    @13
    wceq
    @10
    @0
    @1
    @3
    @1
    @0
    @1
    @2
    simpl
    anim2i
    ancomd
    cF
    cV
    cvv
    cZ
    suppimacnv
    syl
    eqeq1d
    @10
    @14
    @8
    @10
    @14
    @7
    @6
    ccnv
    #
    @12
    cima
    #
    c0
    @10
    @6
    cvv
    wcel
    #
    @0
    wa
    #
    @7
    @16
    wceq
    @10
    @0
    @17
    @3
    @17
    @0
    cF
    cG
    cV
    cW
    coexg
    anim2i
    ancomd
    @6
    cvv
    cvv
    cZ
    suppimacnv
    syl
    @14
    @16
    cG
    ccnv
    #
    @13
    cima
    #
    c0
    @16
    @19
    @11
    ccom
    #
    @12
    cima
    @20
    @15
    @21
    @12
    cF
    cG
    cnvco
    imaeq1i
    @19
    @11
    @12
    imaco
    eqtri
    @14
    @20
    @19
    c0
    cima
    c0
    @13
    c0
    @19
    imaeq2
    @19
    ima0
    syl6eq
    syl5eq
    sylan9eq
    ex
    sylbid
    ex
    @0
    wn
    #
    @8
    @3
    @5
    @22
    @18
    wn
    @8
    @22
    @0
    @17
    @22
    id
    intnand
    @6
    cZ
    supp0prc
    syl
    2a1d
    pm2.61i
end
