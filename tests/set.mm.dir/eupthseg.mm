include "ceupth.mm"
include "cfv.mm"
include "wbr.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "wss.mm"
include "cwlks.mm"
include "cv.mm"
include "wral.mm"
include "wi.mm"
include "cdm.mm"
include "wf1o.mm"
include "eupthi.mm"
include "simpld.mm"
include "wlkvtxeledg.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "preq12d.mm"
include "sseq12d.mm"
include "rspcva.mm"
include "expcom.mm"
include "3syl.mm"
include "imp.mm"

theorem eupthseg
  let cP: class P
  let cF: class F
  let cG: class G
  let cI: class I
  let cN: class N
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p
  let vk: setvar k
  assume eupths.i: |- I = ( iEdg ` G )


  assert |- ( ( F ( EulerPaths ` G ) P /\ N e. ( 0 ..^ ( # ` F ) ) ) -> { ( P ` N ) , ( P ` ( N + 1 ) ) } C_ ( I ` ( F ` N ) ) )

  proof
    cF
    cP
    cG
    ceupth
    cfv
    wbr
    #
    cN
    cc0
    cF
    chash
    cfv
    cfzo
    co
    #
    wcel
    #
    cN
    cP
    cfv
    #
    cN
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cpr
    #
    cN
    cF
    cfv
    #
    cI
    cfv
    #
    wss
    #
    @0
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
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
    cpr
    #
    @11
    cF
    cfv
    #
    cI
    cfv
    #
    wss
    #
    vk
    @1
    wral
    #
    @2
    @9
    wi
    @0
    @10
    @1
    cI
    cdm
    cF
    wf1o
    cP
    cF
    cG
    cI
    eupths.i
    eupthi
    simpld
    cP
    vk
    cF
    cG
    cI
    eupths.i
    wlkvtxeledg
    @2
    @19
    @9
    @18
    @9
    vk
    cN
    @1
    @11
    cN
    wceq
    #
    @15
    @6
    @17
    @8
    @20
    @12
    @3
    @14
    @5
    @11
    cN
    cP
    fveq2
    @20
    @13
    @4
    cP
    @11
    cN
    c1
    caddc
    oveq1
    fveq2d
    preq12d
    @20
    @16
    @7
    cI
    @11
    cN
    cF
    fveq2
    fveq2d
    sseq12d
    rspcva
    expcom
    3syl
    imp
end
