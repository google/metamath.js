include "cprime.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cexp.mm"
include "co.mm"
include "cpc.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cdvds.mm"
include "simpl.mm"
include "cn.mm"
include "prmnn.mm"
include "syl.mm"
include "simpr.mm"
include "nnexpcld.mm"
include "pccld.mm"
include "nn0red.mm"
include "leidd.mm"
include "cz.mm"
include "wb.mm"
include "nnzd.mm"
include "pcdvdsb.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "wi.mm"
include "dvdsle.mm"
include "syl2anc.mm"
include "mpd.mm"
include "nnred.mm"
include "nn0zd.mm"
include "nn0z.mm"
include "adantl.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "c1.mm"
include "clt.mm"
include "prmuz2.mm"
include "eluz2b1.mm"
include "simprbi.mm"
include "leexp2d.mm"
include "mpbird.mm"
include "iddvds.mm"
include "cr.mm"
include "nn0re.mm"
include "letri3d.mm"
include "mpbir2and.mm"

theorem pcidlem
  let cA: class A
  let cP: class P


  assert |- ( ( P e. Prime /\ A e. NN0 ) -> ( P pCnt ( P ^ A ) ) = A )

  proof
    cP
    cprime
    wcel
    #
    cA
    cn0
    wcel
    #
    wa
    #
    cP
    cP
    cA
    cexp
    co
    #
    cpc
    co
    #
    cA
    wceq
    @4
    cA
    cle
    wbr
    #
    cA
    @4
    cle
    wbr
    #
    @2
    @5
    cP
    @4
    cexp
    co
    #
    @3
    cle
    wbr
    #
    @2
    @7
    @3
    cdvds
    wbr
    #
    @8
    @2
    @4
    @4
    cle
    wbr
    #
    @9
    @2
    @4
    @2
    @4
    @2
    cP
    @3
    @0
    @1
    simpl
    #
    @2
    cP
    cA
    @2
    @0
    cP
    cn
    wcel
    @11
    cP
    prmnn
    syl
    #
    @0
    @1
    simpr
    #
    nnexpcld
    #
    pccld
    #
    nn0red
    #
    leidd
    @2
    @0
    @3
    cz
    wcel
    #
    @4
    cn0
    wcel
    @10
    @9
    wb
    @11
    @2
    @3
    @14
    nnzd
    #
    @15
    @4
    cP
    @3
    pcdvdsb
    syl3anc
    mpbid
    @2
    @7
    cz
    wcel
    @3
    cn
    wcel
    @9
    @8
    wi
    @2
    @7
    @2
    cP
    @4
    @12
    @15
    nnexpcld
    nnzd
    @14
    @7
    @3
    dvdsle
    syl2anc
    mpd
    @2
    cP
    @4
    cA
    @2
    cP
    @12
    nnred
    @2
    @4
    @15
    nn0zd
    @1
    cA
    cz
    wcel
    @0
    cA
    nn0z
    adantl
    @2
    cP
    c2
    cuz
    cfv
    wcel
    #
    c1
    cP
    clt
    wbr
    #
    @2
    @0
    @19
    @11
    cP
    prmuz2
    syl
    @19
    cP
    cz
    wcel
    @20
    cP
    eluz2b1
    simprbi
    syl
    leexp2d
    mpbird
    @2
    @6
    @3
    @3
    cdvds
    wbr
    #
    @2
    @17
    @21
    @18
    @3
    iddvds
    syl
    @2
    @0
    @17
    @1
    @6
    @21
    wb
    @11
    @18
    @13
    cA
    cP
    @3
    pcdvdsb
    syl3anc
    mpbird
    @2
    @4
    cA
    @16
    @1
    cA
    cr
    wcel
    @0
    cA
    nn0re
    adantl
    letri3d
    mpbir2and
end
