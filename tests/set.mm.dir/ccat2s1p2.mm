include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "cfv.mm"
include "chash.mm"
include "cmin.mm"
include "cword.mm"
include "caddc.mm"
include "cfzo.mm"
include "wceq.mm"
include "s1cl.mm"
include "adantr.mm"
include "adantl.mm"
include "c2.mm"
include "cz.mm"
include "clt.mm"
include "wbr.mm"
include "1z.mm"
include "2z.mm"
include "1lt2.mm"
include "fzolb.mm"
include "mpbir3an.mm"
include "s1len.mm"
include "oveq12i.mm"
include "1p1e2.mm"
include "eqtri.mm"
include "eleqtrri.mm"
include "a1i.mm"
include "ccatval2.mm"
include "syl3anc.mm"
include "cc0.mm"
include "oveq2i.mm"
include "1m1e0.mm"
include "fveq2d.mm"
include "s1fv.mm"
include "eqtrd.mm"

theorem ccat2s1p2
  let cV: class V
  let cX: class X
  let cY: class Y


  assert |- ( ( X e. V /\ Y e. V ) -> ( ( <" X "> ++ <" Y "> ) ` 1 ) = Y )

  proof
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    wa
    #
    c1
    cX
    cs1
    #
    cY
    cs1
    #
    cconcat
    co
    cfv
    #
    c1
    @3
    chash
    cfv
    #
    cmin
    co
    #
    @4
    cfv
    #
    cY
    @2
    @3
    cV
    cword
    #
    wcel
    #
    @4
    @9
    wcel
    #
    c1
    @6
    @6
    @4
    chash
    cfv
    #
    caddc
    co
    #
    cfzo
    co
    #
    wcel
    #
    @5
    @8
    wceq
    @0
    @10
    @1
    cX
    cV
    s1cl
    adantr
    @1
    @11
    @0
    cY
    cV
    s1cl
    adantl
    @15
    @2
    c1
    c1
    c2
    cfzo
    co
    #
    @14
    c1
    @16
    wcel
    c1
    cz
    wcel
    c2
    cz
    wcel
    c1
    c2
    clt
    wbr
    1z
    2z
    1lt2
    c1
    c2
    fzolb
    mpbir3an
    @6
    c1
    @13
    c2
    cfzo
    cX
    s1len
    #
    @13
    c1
    c1
    caddc
    co
    c2
    @6
    c1
    @12
    c1
    caddc
    @17
    cY
    s1len
    oveq12i
    1p1e2
    eqtri
    oveq12i
    eleqtrri
    a1i
    cV
    @3
    @4
    c1
    ccatval2
    syl3anc
    @1
    @8
    cY
    wceq
    @0
    @1
    @8
    cc0
    @4
    cfv
    cY
    @1
    @7
    cc0
    @4
    @7
    cc0
    wceq
    @1
    @7
    c1
    c1
    cmin
    co
    cc0
    @6
    c1
    c1
    cmin
    @17
    oveq2i
    1m1e0
    eqtri
    a1i
    fveq2d
    cY
    cV
    s1fv
    eqtrd
    adantl
    eqtrd
end
