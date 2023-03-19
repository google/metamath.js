include "ccycls.mm"
include "cfv.mm"
include "wbr.mm"
include "cdm.mm"
include "c2.mm"
include "cv.mm"
include "chash.mm"
include "cle.mm"
include "cpw.mm"
include "crab.mm"
include "wf.mm"
include "c1.mm"
include "wne.mm"
include "cpths.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "cwlks.mm"
include "wi.mm"
include "cyclprop.mm"
include "cycliswlk.mm"
include "caddc.mm"
include "co.mm"
include "cfzo.mm"
include "wral.mm"
include "lfgrwlknloop.mm"
include "wcel.mm"
include "cn.mm"
include "1nn.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "lbfzo0.mm"
include "sylibr.mm"
include "fveq2.mm"
include "oveq1.mm"
include "0p1e1.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "neeq12d.mm"
include "rspcv.mm"
include "syl.mm"
include "impcom.mm"
include "wb.mm"
include "neeq2d.mm"
include "adantl.mm"
include "mpbird.mm"
include "ex.mm"
include "necon2d.mm"
include "com13.mm"
include "sylc.mm"
include "com12.mm"

theorem lfgrn1cycl
  let vx: setvar x
  let cP: class P
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let vk: setvar k
  assume lfgrn1cycl.v: |- V = ( Vtx ` G )
  assume lfgrn1cycl.i: |- I = ( iEdg ` G )

  disjoint F x
  disjoint I x
  disjoint V x
  disjoint F k
  disjoint k x
  disjoint G k
  disjoint I k
  disjoint P k
  disjoint V k
  assert |- ( I : dom I --> { x e. ~P V | 2 <_ ( # ` x ) } -> ( F ( Cycles ` G ) P -> ( # ` F ) =/= 1 ) )

  proof
    cF
    cP
    cG
    ccycls
    cfv
    wbr
    #
    cI
    cdm
    c2
    vx
    cv
    chash
    cfv
    cle
    wbr
    vx
    cV
    cpw
    crab
    cI
    wf
    #
    cF
    chash
    cfv
    #
    c1
    wne
    #
    @0
    cF
    cP
    cG
    cpths
    cfv
    wbr
    #
    cc0
    cP
    cfv
    #
    @2
    cP
    cfv
    #
    wceq
    #
    wa
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    @1
    @3
    wi
    #
    cP
    cF
    cG
    cyclprop
    cP
    cF
    cG
    cycliswlk
    @7
    @8
    @9
    wi
    @4
    @1
    @8
    @7
    @3
    @1
    @8
    @7
    @3
    wi
    #
    @1
    @8
    wa
    vk
    cv
    #
    cP
    cfv
    #
    @11
    c1
    caddc
    co
    #
    cP
    cfv
    #
    wne
    #
    vk
    cc0
    @2
    cfzo
    co
    #
    wral
    #
    @10
    vx
    cP
    vk
    cF
    cG
    cI
    cV
    lfgrn1cycl.i
    lfgrn1cycl.v
    lfgrwlknloop
    @17
    @2
    c1
    @5
    @6
    @17
    @2
    c1
    wceq
    #
    @5
    @6
    wne
    #
    @17
    @18
    wa
    @19
    @5
    c1
    cP
    cfv
    #
    wne
    #
    @18
    @17
    @21
    @18
    cc0
    @16
    wcel
    #
    @17
    @21
    wi
    @18
    @2
    cn
    wcel
    #
    @22
    @18
    @23
    c1
    cn
    wcel
    1nn
    @2
    c1
    cn
    eleq1
    mpbiri
    @2
    lbfzo0
    sylibr
    @15
    @21
    vk
    cc0
    @16
    @11
    cc0
    wceq
    #
    @12
    @5
    @14
    @20
    @11
    cc0
    cP
    fveq2
    @24
    @13
    c1
    cP
    @24
    @13
    cc0
    c1
    caddc
    co
    c1
    @11
    cc0
    c1
    caddc
    oveq1
    0p1e1
    syl6eq
    fveq2d
    neeq12d
    rspcv
    syl
    impcom
    @18
    @19
    @21
    wb
    @17
    @18
    @6
    @20
    @5
    @2
    c1
    cP
    fveq2
    neeq2d
    adantl
    mpbird
    ex
    necon2d
    syl
    ex
    com13
    adantl
    sylc
    com12
end
