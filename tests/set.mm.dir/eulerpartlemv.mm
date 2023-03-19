include "wcel.mm"
include "cn.mm"
include "cn0.mm"
include "wf.mm"
include "ccnv.mm"
include "cima.mm"
include "cfn.mm"
include "cv.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "csu.mm"
include "wceq.mm"
include "w3a.mm"
include "eulerpartleme.mm"
include "wa.mm"
include "c1.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "simpl.mm"
include "sselda.mm"
include "ffvelrnd.mm"
include "nnnn0d.mm"
include "nn0mulcld.mm"
include "nn0cnd.mm"
include "cdif.mm"
include "cc0.mm"
include "wn.mm"
include "wo.mm"
include "simpr.mm"
include "eldifad.mm"
include "wi.mm"
include "eldifbd.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "mtbid.mm"
include "imnan.mm"
include "sylibr.mm"
include "mpd.mm"
include "elnn0.mm"
include "sylib.mm"
include "orel1.mm"
include "sylc.mm"
include "oveq1d.mm"
include "nncnd.mm"
include "mul02d.mm"
include "eqtrd.mm"
include "cuz.mm"
include "wss.mm"
include "nnuz.mm"
include "eqimssi.mm"
include "a1i.mm"
include "sumss.mm"
include "eqcomd.mm"
include "adantr.mm"
include "eqeq1d.mm"
include "pm5.32i.mm"
include "df-3an.mm"
include "3bitr4i.mm"
include "bitri.mm"

theorem eulerpartlemv
  let cA: class A
  let cP: class P
  let vf: setvar f
  let vk: setvar k
  let cN: class N
  assume eulerpart.p: |- P = { f e. ( NN0 ^m NN ) | ( ( `' f " NN ) e. Fin /\ sum_ k e. NN ( ( f ` k ) x. k ) = N ) }

  disjoint f k
  disjoint A f
  disjoint A k
  disjoint N f
  disjoint N k
  disjoint P k
  assert |- ( A e. P <-> ( A : NN --> NN0 /\ ( `' A " NN ) e. Fin /\ sum_ k e. ( `' A " NN ) ( ( A ` k ) x. k ) = N ) )

  proof
    cA
    cP
    wcel
    cn
    cn0
    cA
    wf
    #
    cA
    ccnv
    cn
    cima
    #
    cfn
    wcel
    #
    cn
    vk
    cv
    #
    cA
    cfv
    #
    @3
    cmul
    co
    #
    vk
    csu
    #
    cN
    wceq
    #
    w3a
    #
    @0
    @2
    @1
    @5
    vk
    csu
    #
    cN
    wceq
    #
    w3a
    #
    cA
    cP
    vf
    vk
    cN
    eulerpart.p
    eulerpartleme
    @0
    @2
    wa
    #
    @7
    wa
    @12
    @10
    wa
    @8
    @11
    @12
    @7
    @10
    @12
    @6
    @9
    cN
    @0
    @6
    @9
    wceq
    @2
    @0
    @9
    @6
    @0
    @1
    cn
    @5
    vk
    c1
    @0
    cA
    cdm
    @1
    cn
    cA
    cn
    cnvimass
    cn
    cn0
    cA
    fdm
    syl5sseq
    #
    @0
    @3
    @1
    wcel
    #
    wa
    #
    @5
    @15
    @4
    @3
    @15
    cn
    cn0
    @3
    cA
    @0
    @14
    simpl
    @0
    @1
    cn
    @3
    @13
    sselda
    #
    ffvelrnd
    @15
    @3
    @16
    nnnn0d
    nn0mulcld
    nn0cnd
    @0
    @3
    cn
    @1
    cdif
    wcel
    #
    wa
    #
    @5
    cc0
    @3
    cmul
    co
    cc0
    @18
    @4
    cc0
    @3
    cmul
    @18
    @4
    cn
    wcel
    #
    wn
    #
    @19
    @4
    cc0
    wceq
    #
    wo
    #
    @21
    @18
    @3
    cn
    wcel
    #
    @20
    @18
    @3
    cn
    @1
    @0
    @17
    simpr
    #
    eldifad
    #
    @18
    @23
    @19
    wa
    #
    wn
    @23
    @20
    wi
    @18
    @14
    @26
    @18
    @3
    cn
    @1
    @24
    eldifbd
    @18
    @0
    cA
    cn
    wfn
    @14
    @26
    wb
    @0
    @17
    simpl
    #
    cn
    cn0
    cA
    ffn
    cn
    @3
    cn
    cA
    elpreima
    3syl
    mtbid
    @23
    @19
    imnan
    sylibr
    mpd
    @18
    @4
    cn0
    wcel
    @22
    @18
    cn
    cn0
    @3
    cA
    @27
    @25
    ffvelrnd
    @4
    elnn0
    sylib
    @19
    @21
    orel1
    sylc
    oveq1d
    @18
    @3
    @18
    @3
    @25
    nncnd
    mul02d
    eqtrd
    cn
    c1
    cuz
    cfv
    #
    wss
    @0
    cn
    @28
    nnuz
    eqimssi
    a1i
    sumss
    eqcomd
    adantr
    eqeq1d
    pm5.32i
    @0
    @2
    @7
    df-3an
    @0
    @2
    @10
    df-3an
    3bitr4i
    bitri
end
