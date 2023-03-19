include "cfin2.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "crpss.mm"
include "wor.mm"
include "cuni.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "simpll.mm"
include "elpwi.mm"
include "adantl.mm"
include "simplr.mm"
include "sspwb.mm"
include "sylib.mm"
include "sstrd.mm"
include "fin2i.mm"
include "ex.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "wb.mm"
include "ssexg.mm"
include "ancoms.mm"
include "isfin2.mm"
include "syl.mm"
include "mpbird.mm"

theorem ssfin2
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


  assert |- ( ( A e. Fin2 /\ B C_ A ) -> B e. Fin2 )

  proof
    cA
    cfin2
    wcel
    #
    cB
    cA
    wss
    #
    wa
    #
    cB
    cfin2
    wcel
    #
    vx
    cv
    #
    c0
    wne
    @4
    crpss
    wor
    wa
    #
    @4
    cuni
    @4
    wcel
    #
    wi
    #
    vx
    cB
    cpw
    #
    cpw
    #
    wral
    #
    @2
    @7
    vx
    @9
    @2
    @4
    @9
    wcel
    #
    wa
    #
    @0
    @4
    cA
    cpw
    #
    wss
    #
    @7
    @0
    @1
    @11
    simpll
    @12
    @4
    @8
    @13
    @11
    @4
    @8
    wss
    @2
    @4
    @8
    elpwi
    adantl
    @12
    @1
    @8
    @13
    wss
    @0
    @1
    @11
    simplr
    cB
    cA
    sspwb
    sylib
    sstrd
    @0
    @14
    wa
    @5
    @6
    cA
    @4
    fin2i
    ex
    syl2anc
    ralrimiva
    @2
    cB
    cvv
    wcel
    #
    @3
    @10
    wb
    @1
    @0
    @15
    cB
    cA
    cfin2
    ssexg
    ancoms
    vx
    cB
    cvv
    isfin2
    syl
    mpbird
end
