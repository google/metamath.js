include "caa.mm"
include "wcel.mm"
include "cq.mm"
include "cply.mm"
include "cfv.mm"
include "cdgr.mm"
include "cdgraa.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cc0.mm"
include "wceq.mm"
include "c0p.mm"
include "wne.mm"
include "wn.mm"
include "wa.mm"
include "cle.mm"
include "simpl3.mm"
include "cn0.mm"
include "simpl2.mm"
include "dgrcl.mm"
include "syl.mm"
include "nn0red.mm"
include "cn.mm"
include "simpl1.mm"
include "dgraacl.mm"
include "nnred.mm"
include "ltnled.mm"
include "mpbid.mm"
include "cc.mm"
include "simprl.mm"
include "aacn.mm"
include "simprr.mm"
include "dgraaub.mm"
include "syl22anc.mm"
include "expr.mm"
include "mtod.mm"
include "ex.mm"
include "necon4ad.mm"
include "wi.mm"
include "0pval.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "3ad2ant1.mm"
include "impbid.mm"

theorem dgraa0p
  let cA: class A
  let cP: class P
  let vd: setvar d
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vc: setvar c


  assert |- ( ( A e. AA /\ P e. ( Poly ` QQ ) /\ ( deg ` P ) < ( degAA ` A ) ) -> ( ( P ` A ) = 0 <-> P = 0p ) )

  proof
    cA
    caa
    wcel
    #
    cP
    cq
    cply
    cfv
    wcel
    #
    cP
    cdgr
    cfv
    #
    cA
    cdgraa
    cfv
    #
    clt
    wbr
    #
    w3a
    #
    cA
    cP
    cfv
    #
    cc0
    wceq
    #
    cP
    c0p
    wceq
    #
    @5
    @7
    cP
    c0p
    @5
    cP
    c0p
    wne
    #
    @7
    wn
    @5
    @9
    wa
    #
    @7
    @3
    @2
    cle
    wbr
    #
    @10
    @4
    @11
    wn
    @0
    @1
    @4
    @9
    simpl3
    @10
    @2
    @3
    @10
    @2
    @10
    @1
    @2
    cn0
    wcel
    @0
    @1
    @4
    @9
    simpl2
    cq
    cP
    dgrcl
    syl
    nn0red
    @10
    @3
    @10
    @0
    @3
    cn
    wcel
    @0
    @1
    @4
    @9
    simpl1
    cA
    dgraacl
    syl
    nnred
    ltnled
    mpbid
    @5
    @9
    @7
    @11
    @5
    @9
    @7
    wa
    #
    wa
    #
    @1
    @9
    cA
    cc
    wcel
    #
    @7
    @11
    @0
    @1
    @4
    @12
    simpl2
    @5
    @9
    @7
    simprl
    @13
    @0
    @14
    @0
    @1
    @4
    @12
    simpl1
    cA
    aacn
    #
    syl
    @5
    @9
    @7
    simprr
    cA
    cP
    dgraaub
    syl22anc
    expr
    mtod
    ex
    necon4ad
    @0
    @1
    @8
    @7
    wi
    @4
    @0
    @7
    @8
    cA
    c0p
    cfv
    #
    cc0
    wceq
    #
    @0
    @14
    @17
    @15
    cA
    0pval
    syl
    @8
    @6
    @16
    cc0
    cA
    cP
    c0p
    fveq1
    eqeq1d
    syl5ibrcom
    3ad2ant1
    impbid
end
