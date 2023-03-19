include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cv.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "cn0.mm"
include "wreu.mm"
include "cc0.mm"
include "wne.mm"
include "nnz.mm"
include "nnne0.mm"
include "jca.mm"
include "w3a.mm"
include "cle.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "wrex.mm"
include "divalg.mm"
include "divalgb.mm"
include "mpbid.mm"
include "3expb.mm"
include "sylan2.mm"
include "wb.mm"
include "nnre.mm"
include "nnnn0.mm"
include "nn0ge0d.mm"
include "absidd.mm"
include "breq2d.mm"
include "anbi1d.mm"
include "reubidv.mm"
include "adantl.mm"

theorem divalg2
  let cD: class D
  let cN: class N
  let vr: setvar r
  let vq: setvar q

  disjoint D r
  disjoint N r
  disjoint D q
  disjoint q r
  disjoint N q
  assert |- ( ( N e. ZZ /\ D e. NN ) -> E! r e. NN0 ( r < D /\ D || ( N - r ) ) )

  proof
    cN
    cz
    wcel
    #
    cD
    cn
    wcel
    #
    wa
    vr
    cv
    #
    cD
    cabs
    cfv
    #
    clt
    wbr
    #
    cD
    cN
    @2
    cmin
    co
    cdvds
    wbr
    #
    wa
    #
    vr
    cn0
    wreu
    #
    @2
    cD
    clt
    wbr
    #
    @5
    wa
    #
    vr
    cn0
    wreu
    #
    @1
    @0
    cD
    cz
    wcel
    #
    cD
    cc0
    wne
    #
    wa
    @7
    @1
    @11
    @12
    cD
    nnz
    cD
    nnne0
    jca
    @0
    @11
    @12
    @7
    @0
    @11
    @12
    w3a
    cc0
    @2
    cle
    wbr
    @4
    cN
    vq
    cv
    cD
    cmul
    co
    @2
    caddc
    co
    wceq
    w3a
    vq
    cz
    wrex
    vr
    cz
    wreu
    @7
    cD
    cN
    vr
    vq
    divalg
    cD
    cN
    vr
    vq
    divalgb
    mpbid
    3expb
    sylan2
    @1
    @7
    @10
    wb
    @0
    @1
    @6
    @9
    vr
    cn0
    @1
    @4
    @8
    @5
    @1
    @3
    cD
    @2
    clt
    @1
    cD
    cD
    nnre
    @1
    cD
    cD
    nnnn0
    nn0ge0d
    absidd
    breq2d
    anbi1d
    reubidv
    adantl
    mpbid
end
