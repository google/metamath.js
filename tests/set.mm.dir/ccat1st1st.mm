include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cword.mm"
include "wcel.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "wa.mm"
include "c0.mm"
include "hasheq0.mm"
include "biimpac.mm"
include "cvv.mm"
include "s1cli.mm"
include "ccatlid.mm"
include "ax-mp.mm"
include "fveq1i.mm"
include "0ex.mm"
include "s1fv.mm"
include "eqtri.mm"
include "id.mm"
include "fveq1.mm"
include "0fv.mm"
include "syl6eq.mm"
include "s1eqd.mm"
include "oveq12d.mm"
include "fveq1d.mm"
include "3eqtr4a.mm"
include "syl.mm"
include "wn.mm"
include "cfzo.mm"
include "wrdv.mm"
include "adantl.mm"
include "fvexd.mm"
include "cn.mm"
include "cn0.mm"
include "wi.mm"
include "lencl.mm"
include "wne.mm"
include "df-ne.mm"
include "elnnne0.mm"
include "simplbi2.mm"
include "syl5bir.mm"
include "impcom.mm"
include "lbfzo0.mm"
include "sylibr.mm"
include "ccats1val1.mm"
include "syl3anc.mm"
include "pm2.61ian.mm"

theorem ccat1st1st
  let cV: class V
  let cW: class W


  assert |- ( W e. Word V -> ( ( W ++ <" ( W ` 0 ) "> ) ` 0 ) = ( W ` 0 ) )

  proof
    cW
    chash
    cfv
    #
    cc0
    wceq
    #
    cW
    cV
    cword
    #
    wcel
    #
    cc0
    cW
    cc0
    cW
    cfv
    #
    cs1
    #
    cconcat
    co
    #
    cfv
    #
    @4
    wceq
    #
    @1
    @3
    wa
    cW
    c0
    wceq
    #
    @8
    @3
    @1
    @9
    cW
    @2
    hasheq0
    biimpac
    @9
    cc0
    c0
    c0
    cs1
    #
    cconcat
    co
    #
    cfv
    #
    c0
    @7
    @4
    @12
    cc0
    @10
    cfv
    #
    c0
    cc0
    @11
    @10
    @10
    cvv
    cword
    #
    wcel
    @11
    @10
    wceq
    c0
    s1cli
    cvv
    @10
    ccatlid
    ax-mp
    fveq1i
    c0
    cvv
    wcel
    @13
    c0
    wceq
    0ex
    c0
    cvv
    s1fv
    ax-mp
    eqtri
    @9
    cc0
    @6
    @11
    @9
    cW
    c0
    @5
    @10
    cconcat
    @9
    id
    @9
    @4
    c0
    @9
    @4
    cc0
    c0
    cfv
    c0
    cc0
    cW
    c0
    fveq1
    cc0
    0fv
    syl6eq
    #
    s1eqd
    oveq12d
    fveq1d
    @15
    3eqtr4a
    syl
    @1
    wn
    #
    @3
    wa
    #
    cW
    @14
    wcel
    #
    @4
    cvv
    wcel
    cc0
    cc0
    @0
    cfzo
    co
    wcel
    #
    @8
    @3
    @18
    @16
    cV
    cW
    wrdv
    adantl
    @17
    cc0
    cW
    fvexd
    @17
    @0
    cn
    wcel
    #
    @19
    @3
    @16
    @20
    @3
    @0
    cn0
    wcel
    #
    @16
    @20
    wi
    cV
    cW
    lencl
    @16
    @0
    cc0
    wne
    #
    @21
    @20
    @0
    cc0
    df-ne
    @20
    @21
    @22
    @0
    elnnne0
    simplbi2
    syl5bir
    syl
    impcom
    @0
    lbfzo0
    sylibr
    @4
    cc0
    cvv
    cW
    ccats1val1
    syl3anc
    pm2.61ian
end
