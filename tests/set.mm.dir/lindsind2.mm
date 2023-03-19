include "clmod.mm"
include "wcel.mm"
include "cnzr.mm"
include "wa.mm"
include "clinds.mm"
include "cfv.mm"
include "w3a.mm"
include "cid.mm"
include "cres.mm"
include "cdm.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "clindf.mm"
include "wbr.mm"
include "wn.mm"
include "simp1.mm"
include "linds2.mm"
include "3ad2ant2.mm"
include "dmresi.mm"
include "eleq2i.mm"
include "biimpri.mm"
include "3ad2ant3.mm"
include "lindfind2.mm"
include "syl3anc.mm"
include "wb.mm"
include "fvresi.mm"
include "wceq.mm"
include "difeq1i.mm"
include "imaeq2i.mm"
include "wss.mm"
include "difss.mm"
include "resiima.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "a1i.mm"
include "eleq12d.mm"
include "mtbid.mm"

theorem lindsind2
  let cE: class E
  let cF: class F
  let cK: class K
  let cL: class L
  let cW: class W
  assume lindfind2.k: |- K = ( LSpan ` W )
  assume lindfind2.l: |- L = ( Scalar ` W )


  assert |- ( ( ( W e. LMod /\ L e. NzRing ) /\ F e. ( LIndS ` W ) /\ E e. F ) -> -. E e. ( K ` ( F \ { E } ) ) )

  proof
    cW
    clmod
    wcel
    cL
    cnzr
    wcel
    wa
    #
    cF
    cW
    clinds
    cfv
    wcel
    #
    cE
    cF
    wcel
    #
    w3a
    #
    cE
    cid
    cF
    cres
    #
    cfv
    #
    @4
    @4
    cdm
    #
    cE
    csn
    #
    cdif
    #
    cima
    #
    cK
    cfv
    #
    wcel
    #
    cE
    cF
    @7
    cdif
    #
    cK
    cfv
    #
    wcel
    #
    @3
    @0
    @4
    cW
    clindf
    wbr
    #
    cE
    @6
    wcel
    #
    @11
    wn
    @0
    @1
    @2
    simp1
    @1
    @0
    @15
    @2
    cW
    cF
    linds2
    3ad2ant2
    @2
    @0
    @16
    @1
    @16
    @2
    @6
    cF
    cE
    cF
    dmresi
    #
    eleq2i
    biimpri
    3ad2ant3
    cE
    @4
    cK
    cL
    cW
    lindfind2.k
    lindfind2.l
    lindfind2
    syl3anc
    @2
    @0
    @11
    @14
    wb
    @1
    @2
    @5
    cE
    @10
    @13
    cF
    cE
    fvresi
    @10
    @13
    wceq
    @2
    @9
    @12
    cK
    @9
    @4
    @12
    cima
    #
    @12
    @8
    @12
    @4
    @6
    cF
    @7
    @17
    difeq1i
    imaeq2i
    @12
    cF
    wss
    @18
    @12
    wceq
    cF
    @7
    difss
    cF
    @12
    resiima
    ax-mp
    eqtri
    fveq2i
    a1i
    eleq12d
    3ad2ant3
    mtbid
end
