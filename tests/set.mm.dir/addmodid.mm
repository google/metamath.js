include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "cmo.mm"
include "c1.mm"
include "cmul.mm"
include "wceq.mm"
include "nncn.mm"
include "mulid2d.mm"
include "3ad2ant2.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "cz.mm"
include "crp.mm"
include "cc0.mm"
include "cico.mm"
include "1zzd.mm"
include "nnrp.mm"
include "cxr.mm"
include "cle.mm"
include "nn0re.mm"
include "rexrd.mm"
include "3ad2ant1.mm"
include "nn0ge0.mm"
include "simp3.mm"
include "wb.mm"
include "0xr.mm"
include "nnre.mm"
include "elico1.mm"
include "sylancr.mm"
include "mpbir3and.mm"
include "muladdmodid.mm"
include "syl3anc.mm"
include "eqtrd.mm"

theorem addmodid
  let cA: class A
  let cM: class M


  assert |- ( ( A e. NN0 /\ M e. NN /\ A < M ) -> ( ( M + A ) mod M ) = A )

  proof
    cA
    cn0
    wcel
    #
    cM
    cn
    wcel
    #
    cA
    cM
    clt
    wbr
    #
    w3a
    #
    cM
    cA
    caddc
    co
    #
    cM
    cmo
    co
    c1
    cM
    cmul
    co
    #
    cA
    caddc
    co
    #
    cM
    cmo
    co
    #
    cA
    @3
    @4
    @6
    cM
    cmo
    @3
    cM
    @5
    cA
    caddc
    @3
    @5
    cM
    @1
    @0
    @5
    cM
    wceq
    @2
    @1
    cM
    cM
    nncn
    mulid2d
    3ad2ant2
    eqcomd
    oveq1d
    oveq1d
    @3
    c1
    cz
    wcel
    cM
    crp
    wcel
    #
    cA
    cc0
    cM
    cico
    co
    wcel
    #
    @7
    cA
    wceq
    @3
    1zzd
    @1
    @0
    @8
    @2
    cM
    nnrp
    3ad2ant2
    @3
    @9
    cA
    cxr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    @2
    @0
    @1
    @10
    @2
    @0
    cA
    cA
    nn0re
    rexrd
    3ad2ant1
    @0
    @1
    @11
    @2
    cA
    nn0ge0
    3ad2ant1
    @0
    @1
    @2
    simp3
    @3
    cc0
    cxr
    wcel
    cM
    cxr
    wcel
    #
    @9
    @10
    @11
    @2
    w3a
    wb
    0xr
    @1
    @0
    @12
    @2
    @1
    cM
    cM
    nnre
    rexrd
    3ad2ant2
    cc0
    cM
    cA
    elico1
    sylancr
    mpbir3and
    cA
    cM
    c1
    muladdmodid
    syl3anc
    eqtrd
end
