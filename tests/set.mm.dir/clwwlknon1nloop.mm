include "wcel.mm"
include "csn.mm"
include "wnel.mm"
include "c1.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cs1.mm"
include "cword.mm"
include "crab.mm"
include "clwwlknon1.mm"
include "adantr.mm"
include "wn.mm"
include "wral.mm"
include "wo.mm"
include "df-nel.mm"
include "biimpi.mm"
include "olcd.mm"
include "ad2antlr.mm"
include "ianor.mm"
include "sylibr.mm"
include "ralrimiva.mm"
include "rabeq0.mm"
include "eqtrd.mm"
include "cclwwlknon.mm"
include "cfv.mm"
include "oveqi.mm"
include "cvtx.mm"
include "cn.mm"
include "eleq2i.mm"
include "notbii.mm"
include "intnanrd.mm"
include "clwwlknon0.mm"
include "syl.mm"
include "syl5eq.mm"
include "pm2.61ian.mm"

theorem clwwlknon1nloop
  let cC: class C
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let vw: setvar w
  assume clwwlknon1.v: |- V = ( Vtx ` G )
  assume clwwlknon1.c: |- C = ( ClWWalksNOn ` G )
  assume clwwlknon1.e: |- E = ( Edg ` G )


  assert |- ( { X } e/ E -> ( X C 1 ) = (/) )

  proof
    cX
    cV
    wcel
    #
    cX
    csn
    #
    cE
    wnel
    #
    cX
    c1
    cC
    co
    #
    c0
    wceq
    #
    @0
    @2
    wa
    #
    @3
    vw
    cv
    #
    cX
    cs1
    wceq
    #
    @1
    cE
    wcel
    #
    wa
    #
    vw
    cV
    cword
    #
    crab
    #
    c0
    @0
    @3
    @11
    wceq
    @2
    vw
    cC
    cE
    cG
    cV
    cX
    clwwlknon1.v
    clwwlknon1.c
    clwwlknon1.e
    clwwlknon1
    adantr
    @5
    @9
    wn
    #
    vw
    @10
    wral
    @11
    c0
    wceq
    @5
    @12
    vw
    @10
    @5
    @6
    @10
    wcel
    #
    wa
    @7
    wn
    #
    @8
    wn
    #
    wo
    #
    @12
    @2
    @16
    @0
    @13
    @2
    @15
    @14
    @2
    @15
    @1
    cE
    df-nel
    biimpi
    olcd
    ad2antlr
    @7
    @8
    ianor
    sylibr
    ralrimiva
    @9
    vw
    @10
    rabeq0
    sylibr
    eqtrd
    @0
    wn
    #
    @4
    @2
    @17
    @3
    cX
    c1
    cG
    cclwwlknon
    cfv
    #
    co
    #
    c0
    cC
    @18
    cX
    c1
    clwwlknon1.c
    oveqi
    @17
    cX
    cG
    cvtx
    cfv
    #
    wcel
    #
    c1
    cn
    wcel
    #
    wa
    wn
    @19
    c0
    wceq
    @17
    @21
    @22
    @17
    @21
    wn
    @0
    @21
    cV
    @20
    cX
    clwwlknon1.v
    eleq2i
    notbii
    biimpi
    intnanrd
    cG
    c1
    cX
    clwwlknon0
    syl
    syl5eq
    adantr
    pm2.61ian
end
