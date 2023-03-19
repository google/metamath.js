include "chmeo.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cima.mm"
include "ccnv.mm"
include "hmeoima.mm"
include "ccn.mm"
include "hmeocn.mm"
include "cnima.mm"
include "sylan.mm"
include "wa.mm"
include "wceq.mm"
include "cuni.mm"
include "wf1.mm"
include "wss.mm"
include "wb.mm"
include "wf1o.mm"
include "eqid.mm"
include "hmeof1o.mm"
include "adantr.mm"
include "f1of1.mm"
include "syl.mm"
include "elssuni.mm"
include "ad2antrl.mm"
include "cdm.mm"
include "cnvimass.mm"
include "f1dm.mm"
include "syl5sseq.mm"
include "f1imaeq.mm"
include "syl12anc.mm"
include "wfo.mm"
include "f1ofo.mm"
include "ad2antll.mm"
include "foimacnv.mm"
include "syl2anc.mm"
include "eqeq2d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "bitr3d.mm"
include "f1o2d.mm"

theorem hmeoimaf1o
  let vx: setvar x
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let vy: setvar y
  assume hmeoimaf1o.1: |- G = ( x e. J |-> ( F " x ) )

  disjoint F x
  disjoint J x
  disjoint K x
  disjoint x y
  disjoint F y
  disjoint J y
  disjoint K y
  assert |- ( F e. ( J Homeo K ) -> G : J -1-1-onto-> K )

  proof
    cF
    cJ
    cK
    chmeo
    co
    wcel
    #
    vx
    vy
    cJ
    cK
    cF
    vx
    cv
    #
    cima
    #
    cF
    ccnv
    vy
    cv
    #
    cima
    #
    cG
    hmeoimaf1o.1
    @1
    cF
    cJ
    cK
    hmeoima
    @0
    cF
    cJ
    cK
    ccn
    co
    wcel
    @3
    cK
    wcel
    #
    @4
    cJ
    wcel
    cF
    cJ
    cK
    hmeocn
    @3
    cF
    cJ
    cK
    cnima
    sylan
    @0
    @1
    cJ
    wcel
    #
    @5
    wa
    #
    wa
    #
    @2
    cF
    @4
    cima
    #
    wceq
    #
    @1
    @4
    wceq
    #
    @3
    @2
    wceq
    #
    @8
    cJ
    cuni
    #
    cK
    cuni
    #
    cF
    wf1
    #
    @1
    @13
    wss
    #
    @4
    @13
    wss
    @10
    @11
    wb
    @8
    @13
    @14
    cF
    wf1o
    #
    @15
    @0
    @17
    @7
    cF
    cJ
    cK
    @13
    @14
    @13
    eqid
    @14
    eqid
    hmeof1o
    adantr
    #
    @13
    @14
    cF
    f1of1
    syl
    #
    @6
    @16
    @0
    @5
    @1
    cJ
    elssuni
    ad2antrl
    @8
    cF
    cdm
    #
    @4
    @13
    cF
    @3
    cnvimass
    @8
    @15
    @20
    @13
    wceq
    @19
    @13
    @14
    cF
    f1dm
    syl
    syl5sseq
    @13
    @14
    @1
    @4
    cF
    f1imaeq
    syl12anc
    @8
    @10
    @2
    @3
    wceq
    @12
    @8
    @9
    @3
    @2
    @8
    @13
    @14
    cF
    wfo
    #
    @3
    @14
    wss
    #
    @9
    @3
    wceq
    @8
    @17
    @21
    @18
    @13
    @14
    cF
    f1ofo
    syl
    @5
    @22
    @0
    @6
    @3
    cK
    elssuni
    ad2antll
    @13
    @14
    @3
    cF
    foimacnv
    syl2anc
    eqeq2d
    @2
    @3
    eqcom
    syl6bb
    bitr3d
    f1o2d
end
