include "cc.mm"
include "cz.mm"
include "cn.mm"
include "cdif.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "cneg.mm"
include "cn0.mm"
include "eldif.mm"
include "cr.mm"
include "wo.mm"
include "elznn.mm"
include "simprbi.mm"
include "orcanai.mm"
include "wceq.mm"
include "negneg.mm"
include "adantr.mm"
include "nn0negz.mm"
include "adantl.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "wi.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "nngt0.mm"
include "nnre.mm"
include "lt0neg2d.mm"
include "mpbid.mm"
include "wb.mm"
include "renegcld.mm"
include "0re.mm"
include "ltnle.mm"
include "sylancl.mm"
include "nn0ge0.mm"
include "nsyl3.mm"
include "a1i.mm"
include "jcad.mm"
include "impbid2.mm"
include "syl5bb.mm"
include "notbid.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem eldmgm
  let cA: class A


  assert |- ( A e. ( CC \ ( ZZ \ NN ) ) <-> ( A e. CC /\ -. -u A e. NN0 ) )

  proof
    cA
    cc
    cz
    cn
    cdif
    #
    cdif
    wcel
    cA
    cc
    wcel
    #
    cA
    @0
    wcel
    #
    wn
    #
    wa
    @1
    cA
    cneg
    #
    cn0
    wcel
    #
    wn
    #
    wa
    cA
    cc
    @0
    eldif
    @1
    @3
    @6
    @1
    @2
    @5
    @2
    cA
    cz
    wcel
    #
    cA
    cn
    wcel
    #
    wn
    #
    wa
    #
    @1
    @5
    cA
    cz
    cn
    eldif
    @1
    @10
    @5
    @7
    @8
    @5
    @7
    cA
    cr
    wcel
    @8
    @5
    wo
    cA
    elznn
    simprbi
    orcanai
    @1
    @5
    @7
    @9
    @1
    @5
    @7
    @1
    @5
    wa
    @4
    cneg
    #
    cA
    cz
    @1
    @11
    cA
    wceq
    @5
    cA
    negneg
    adantr
    @5
    @11
    cz
    wcel
    @1
    @4
    nn0negz
    adantl
    eqeltrrd
    ex
    @5
    @9
    wi
    @1
    @8
    cc0
    @4
    cle
    wbr
    #
    @5
    @8
    @4
    cc0
    clt
    wbr
    #
    @12
    wn
    #
    @8
    cc0
    cA
    clt
    wbr
    @13
    cA
    nngt0
    @8
    cA
    cA
    nnre
    #
    lt0neg2d
    mpbid
    @8
    @4
    cr
    wcel
    cc0
    cr
    wcel
    @13
    @14
    wb
    @8
    cA
    @15
    renegcld
    0re
    @4
    cc0
    ltnle
    sylancl
    mpbid
    @4
    nn0ge0
    nsyl3
    a1i
    jcad
    impbid2
    syl5bb
    notbid
    pm5.32i
    bitri
end
