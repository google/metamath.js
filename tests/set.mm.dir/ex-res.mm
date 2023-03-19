include "c2.mm"
include "c6.mm"
include "cop.mm"
include "c3.mm"
include "c9.mm"
include "cpr.mm"
include "wceq.mm"
include "c1.mm"
include "wa.mm"
include "cres.mm"
include "csn.mm"
include "cun.mm"
include "simpl.mm"
include "df-pr.mm"
include "syl6eq.mm"
include "reseq1d.mm"
include "resundir.mm"
include "c0.mm"
include "wrel.mm"
include "cdm.mm"
include "wss.mm"
include "cr.mm"
include "2re.mm"
include "elexi.mm"
include "6re.mm"
include "relsnop.mm"
include "dmsnopss.mm"
include "snsspr2.mm"
include "simpr.mm"
include "syl5sseqr.mm"
include "syl5ss.mm"
include "relssres.mm"
include "sylancr.mm"
include "wcel.mm"
include "wn.mm"
include "1re.mm"
include "1lt3.mm"
include "gtneii.mm"
include "2lt3.mm"
include "nelpri.mm"
include "eleq2d.mm"
include "mtbiri.mm"
include "ressnop0.mm"
include "syl.mm"
include "uneq12d.mm"
include "un0.mm"
include "eqtrd.mm"

theorem ex-res
  let cB: class B
  let cF: class F


  assert |- ( ( F = { <. 2 , 6 >. , <. 3 , 9 >. } /\ B = { 1 , 2 } ) -> ( F |` B ) = { <. 2 , 6 >. } )

  proof
    cF
    c2
    c6
    cop
    #
    c3
    c9
    cop
    #
    cpr
    #
    wceq
    #
    cB
    c1
    c2
    cpr
    #
    wceq
    #
    wa
    #
    cF
    cB
    cres
    #
    @0
    csn
    #
    cB
    cres
    #
    @1
    csn
    #
    cB
    cres
    #
    cun
    #
    @8
    @6
    @7
    @8
    @10
    cun
    #
    cB
    cres
    @12
    @6
    cF
    @13
    cB
    @6
    cF
    @2
    @13
    @3
    @5
    simpl
    @0
    @1
    df-pr
    syl6eq
    reseq1d
    @8
    @10
    cB
    resundir
    syl6eq
    @6
    @12
    @8
    c0
    cun
    @8
    @6
    @9
    @8
    @11
    c0
    @6
    @8
    wrel
    @8
    cdm
    #
    cB
    wss
    @9
    @8
    wceq
    c2
    c6
    c2
    cr
    2re
    elexi
    c6
    cr
    6re
    elexi
    relsnop
    @6
    @14
    c2
    csn
    #
    cB
    c2
    c6
    dmsnopss
    @6
    @4
    @15
    cB
    c1
    c2
    snsspr2
    @3
    @5
    simpr
    #
    syl5sseqr
    syl5ss
    @8
    cB
    relssres
    sylancr
    @6
    c3
    cB
    wcel
    #
    wn
    @11
    c0
    wceq
    @6
    @17
    c3
    @4
    wcel
    c3
    c1
    c2
    c1
    c3
    1re
    1lt3
    gtneii
    c2
    c3
    2re
    2lt3
    gtneii
    nelpri
    @6
    cB
    @4
    c3
    @16
    eleq2d
    mtbiri
    c3
    c9
    cB
    ressnop0
    syl
    uneq12d
    @8
    un0
    syl6eq
    eqtrd
end
