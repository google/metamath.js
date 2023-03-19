include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "clcm.mm"
include "co.mm"
include "cle.mm"
include "cv.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "lcmn0val.mm"
include "3adantl1.mm"
include "adantr.mm"
include "wi.mm"
include "breq2.mm"
include "anbi12d.mm"
include "elrab.mm"
include "c1.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "ssrab2.mm"
include "nnuz.mm"
include "sseqtri.mm"
include "infssuzle.mm"
include "mpan.mm"
include "sylbir.mm"
include "ex.mm"
include "3ad2ant1.mm"
include "imp.mm"
include "eqbrtrd.mm"

theorem lcmledvds
  let cK: class K
  let cM: class M
  let cN: class N
  let vn: setvar n


  assert |- ( ( ( K e. NN /\ M e. ZZ /\ N e. ZZ ) /\ -. ( M = 0 \/ N = 0 ) ) -> ( ( M || K /\ N || K ) -> ( M lcm N ) <_ K ) )

  proof
    cK
    cn
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    #
    cM
    cc0
    wceq
    cN
    cc0
    wceq
    wo
    wn
    #
    wa
    #
    cM
    cK
    cdvds
    wbr
    #
    cN
    cK
    cdvds
    wbr
    #
    wa
    #
    cM
    cN
    clcm
    co
    #
    cK
    cle
    wbr
    @5
    @8
    wa
    @9
    cM
    vn
    cv
    #
    cdvds
    wbr
    #
    cN
    @10
    cdvds
    wbr
    #
    wa
    #
    vn
    cn
    crab
    #
    cr
    clt
    cinf
    #
    cK
    cle
    @5
    @9
    @15
    wceq
    #
    @8
    @1
    @2
    @4
    @16
    @0
    vn
    cM
    cN
    lcmn0val
    3adantl1
    adantr
    @5
    @8
    @15
    cK
    cle
    wbr
    #
    @3
    @8
    @17
    wi
    #
    @4
    @0
    @1
    @18
    @2
    @0
    @8
    @17
    @0
    @8
    wa
    cK
    @14
    wcel
    #
    @17
    @13
    @8
    vn
    cK
    cn
    @10
    cK
    wceq
    @11
    @6
    @12
    @7
    @10
    cK
    cM
    cdvds
    breq2
    @10
    cK
    cN
    cdvds
    breq2
    anbi12d
    elrab
    @14
    c1
    cuz
    cfv
    #
    wss
    @19
    @17
    @14
    cn
    @20
    @13
    vn
    cn
    ssrab2
    nnuz
    sseqtri
    cK
    @14
    c1
    infssuzle
    mpan
    sylbir
    ex
    3ad2ant1
    adantr
    imp
    eqbrtrd
    ex
end
