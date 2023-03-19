include "cabl.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "wbr.mm"
include "cminusg.mm"
include "cfv.mm"
include "cplusg.mm"
include "co.mm"
include "w3a.mm"
include "eqid.mm"
include "eqgval.mm"
include "wceq.mm"
include "simpll.mm"
include "cgrp.mm"
include "ablgrp.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "simprr.mm"
include "ablcom.mm"
include "syl3anc.mm"
include "grpsubval.mm"
include "eqtr4d.mm"
include "eleq1d.mm"
include "pm5.32da.mm"
include "df-3an.mm"
include "3bitr4g.mm"
include "bitrd.mm"

theorem eqgabl
  let cA: class A
  let cB: class B
  let c.sm: class .~
  let cS: class S
  let cG: class G
  let c.mi: class .-
  let cX: class X
  assume eqgabl.x: |- X = ( Base ` G )
  assume eqgabl.n: |- .- = ( -g ` G )
  assume eqgabl.r: |- .~ = ( G ~QG S )


  assert |- ( ( G e. Abel /\ S C_ X ) -> ( A .~ B <-> ( A e. X /\ B e. X /\ ( B .- A ) e. S ) ) )

  proof
    cG
    cabl
    wcel
    #
    cS
    cX
    wss
    #
    wa
    #
    cA
    cB
    c.sm
    wbr
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cA
    cG
    cminusg
    cfv
    #
    cfv
    #
    cB
    cG
    cplusg
    cfv
    #
    co
    #
    cS
    wcel
    #
    w3a
    #
    @3
    @4
    cB
    cA
    c.mi
    co
    #
    cS
    wcel
    #
    w3a
    #
    cA
    cB
    @7
    c.sm
    cS
    cG
    @5
    cabl
    cX
    eqgabl.x
    @5
    eqid
    #
    @7
    eqid
    #
    eqgabl.r
    eqgval
    @2
    @3
    @4
    wa
    #
    @9
    wa
    @16
    @12
    wa
    @10
    @13
    @2
    @16
    @9
    @12
    @2
    @16
    wa
    #
    @8
    @11
    cS
    @17
    @8
    cB
    @6
    @7
    co
    #
    @11
    @17
    @0
    @6
    cX
    wcel
    #
    @4
    @8
    @18
    wceq
    @0
    @1
    @16
    simpll
    @17
    cG
    cgrp
    wcel
    #
    @3
    @19
    @0
    @20
    @1
    @16
    cG
    ablgrp
    ad2antrr
    @2
    @3
    @4
    simprl
    #
    cX
    cG
    @5
    cA
    eqgabl.x
    @14
    grpinvcl
    syl2anc
    @2
    @3
    @4
    simprr
    #
    cX
    @7
    cG
    @6
    cB
    eqgabl.x
    @15
    ablcom
    syl3anc
    @17
    @4
    @3
    @11
    @18
    wceq
    @22
    @21
    cX
    @7
    cG
    @5
    c.mi
    cB
    cA
    eqgabl.x
    @15
    @14
    eqgabl.n
    grpsubval
    syl2anc
    eqtr4d
    eleq1d
    pm5.32da
    @3
    @4
    @9
    df-3an
    @3
    @4
    @12
    df-3an
    3bitr4g
    bitrd
end
