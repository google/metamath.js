include "chl.mm"
include "wcel.mm"
include "ccld.mm"
include "cfv.mm"
include "wa.mm"
include "cphl.mm"
include "hlphl.mm"
include "csslss.mm"
include "sylan.mm"
include "ccph.mm"
include "hlcph.mm"
include "csscld.mm"
include "jca.mm"
include "w3a.mm"
include "cpj.mm"
include "cdm.mm"
include "wss.mm"
include "3ad2ant1.mm"
include "eqid.mm"
include "pjcss.mm"
include "syl.mm"
include "pjth2.mm"
include "sseldd.mm"
include "3expb.mm"
include "impbida.mm"

theorem cldcss
  let cC: class C
  let cU: class U
  let cJ: class J
  let cL: class L
  let cV: class V
  let cW: class W
  let vx: setvar x
  assume cldcss.v: |- V = ( Base ` W )
  assume cldcss.j: |- J = ( TopOpen ` W )
  assume cldcss.l: |- L = ( LSubSp ` W )
  assume cldcss.c: |- C = ( CSubSp ` W )


  assert |- ( W e. CHil -> ( U e. C <-> ( U e. L /\ U e. ( Clsd ` J ) ) ) )

  proof
    cW
    chl
    wcel
    #
    cU
    cC
    wcel
    #
    cU
    cL
    wcel
    #
    cU
    cJ
    ccld
    cfv
    wcel
    #
    wa
    @0
    @1
    wa
    @2
    @3
    @0
    cW
    cphl
    wcel
    #
    @1
    @2
    cW
    hlphl
    #
    cC
    cU
    cL
    cW
    cldcss.c
    cldcss.l
    csslss
    sylan
    @0
    cW
    ccph
    wcel
    @1
    @3
    cW
    hlcph
    cC
    cU
    cJ
    cW
    cldcss.c
    cldcss.j
    csscld
    sylan
    jca
    @0
    @2
    @3
    @1
    @0
    @2
    @3
    w3a
    #
    cW
    cpj
    cfv
    #
    cdm
    #
    cC
    cU
    @6
    @4
    @8
    cC
    wss
    @0
    @2
    @4
    @3
    @5
    3ad2ant1
    cC
    @7
    cW
    @7
    eqid
    #
    cldcss.c
    pjcss
    syl
    cU
    cJ
    @7
    cL
    cW
    cldcss.j
    cldcss.l
    @9
    pjth2
    sseldd
    3expb
    impbida
end
