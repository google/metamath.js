include "cfin2.mm"
include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "crpss.mm"
include "wor.mm"
include "cv.mm"
include "wpss.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "cint.mm"
include "cdif.mm"
include "crab.mm"
include "simplr.mm"
include "cuni.mm"
include "simpll.mm"
include "ssrab2.mm"
include "a1i.mm"
include "simprl.mm"
include "fin23lem7.mm"
include "syl3anc.mm"
include "sorpsscmpl.mm"
include "ad2antll.mm"
include "fin2i.mm"
include "syl22anc.mm"
include "wb.mm"
include "sorpssuni.mm"
include "syl.mm"
include "mpbird.mm"
include "psseq2.mm"
include "pssdifcom2.mm"
include "fin23lem11.mm"
include "sylc.mm"
include "sorpssint.mm"
include "mpbid.mm"

theorem fin2i2
  let cA: class A
  let cB: class B
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cV: class V


  assert |- ( ( ( A e. Fin2 /\ B C_ ~P A ) /\ ( B =/= (/) /\ [C.] Or B ) ) -> |^| B e. B )

  proof
    cA
    cfin2
    wcel
    #
    cB
    cA
    cpw
    #
    wss
    #
    wa
    #
    cB
    c0
    wne
    #
    cB
    crpss
    wor
    #
    wa
    #
    wa
    #
    vw
    cv
    #
    vz
    cv
    #
    wpss
    #
    wn
    vw
    cB
    wral
    vz
    cB
    wrex
    #
    cB
    cint
    cB
    wcel
    #
    @7
    @2
    vm
    cv
    #
    vn
    cv
    #
    wpss
    #
    wn
    vn
    cA
    vc
    cv
    cdif
    cB
    wcel
    #
    vc
    @1
    crab
    #
    wral
    vm
    @17
    wrex
    #
    @11
    @0
    @2
    @6
    simplr
    #
    @7
    @18
    @17
    cuni
    @17
    wcel
    #
    @7
    @0
    @17
    @1
    wss
    #
    @17
    c0
    wne
    #
    @17
    crpss
    wor
    #
    @20
    @0
    @2
    @6
    simpll
    #
    @21
    @7
    @16
    vc
    @1
    ssrab2
    a1i
    @7
    @0
    @2
    @4
    @22
    @24
    @19
    @3
    @4
    @5
    simprl
    vc
    cA
    cB
    cfin2
    fin23lem7
    syl3anc
    @5
    @23
    @3
    @4
    vc
    cA
    cB
    sorpsscmpl
    ad2antll
    #
    cA
    @17
    fin2i
    syl22anc
    @7
    @23
    @18
    @20
    wb
    @25
    vn
    vm
    @17
    sorpssuni
    syl
    mpbird
    @15
    @10
    @8
    cA
    @13
    cdif
    #
    wpss
    @13
    cA
    @8
    cdif
    #
    wpss
    vm
    vz
    vn
    vw
    cA
    cB
    vc
    @9
    @26
    @8
    psseq2
    @14
    @27
    @13
    psseq2
    @13
    @8
    cA
    pssdifcom2
    fin23lem11
    sylc
    @5
    @11
    @12
    wb
    @3
    @4
    vw
    vz
    cB
    sorpssint
    ad2antll
    mpbid
end
