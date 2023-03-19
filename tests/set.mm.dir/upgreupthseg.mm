include "cupgr.mm"
include "wcel.mm"
include "ceupth.mm"
include "cfv.mm"
include "wbr.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "wceq.mm"
include "wa.mm"
include "cdm.mm"
include "wf1o.mm"
include "cfz.mm"
include "cvtx.mm"
include "wf.mm"
include "cv.mm"
include "wral.mm"
include "w3a.mm"
include "wi.mm"
include "eqid.mm"
include "upgreupthi.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq1.mm"
include "preq12d.mm"
include "eqeq12d.mm"
include "rspcva.mm"
include "expcom.mm"
include "3ad2ant3.mm"
include "syl.mm"
include "3impia.mm"

theorem upgreupthseg
  let cP: class P
  let cF: class F
  let cG: class G
  let cI: class I
  let cN: class N
  let vn: setvar n
  assume upgreupthseg.i: |- I = ( iEdg ` G )


  assert |- ( ( G e. UPGraph /\ F ( EulerPaths ` G ) P /\ N e. ( 0 ..^ ( # ` F ) ) ) -> ( I ` ( F ` N ) ) = { ( P ` N ) , ( P ` ( N + 1 ) ) } )

  proof
    cG
    cupgr
    wcel
    #
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
    #
    cfzo
    co
    #
    wcel
    #
    cN
    cF
    cfv
    #
    cI
    cfv
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
    wceq
    #
    @0
    @1
    wa
    @3
    cI
    cdm
    cF
    wf1o
    #
    cc0
    @2
    cfz
    co
    cG
    cvtx
    cfv
    #
    cP
    wf
    #
    vn
    cv
    #
    cF
    cfv
    #
    cI
    cfv
    #
    @15
    cP
    cfv
    #
    @15
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cpr
    #
    wceq
    #
    vn
    @3
    wral
    #
    w3a
    @4
    @11
    wi
    #
    cP
    vn
    cF
    cG
    cI
    @13
    upgreupthseg.i
    @13
    eqid
    upgreupthi
    @23
    @12
    @24
    @14
    @4
    @23
    @11
    @22
    @11
    vn
    cN
    @3
    @15
    cN
    wceq
    #
    @17
    @6
    @21
    @10
    @25
    @16
    @5
    cI
    @15
    cN
    cF
    fveq2
    fveq2d
    @25
    @18
    @7
    @20
    @9
    @15
    cN
    cP
    fveq2
    @25
    @19
    @8
    cP
    @15
    cN
    c1
    caddc
    oveq1
    fveq2d
    preq12d
    eqeq12d
    rspcva
    expcom
    3ad2ant3
    syl
    3impia
end
