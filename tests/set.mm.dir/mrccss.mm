include "cphl.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "cmre.mm"
include "cssmre.mm"
include "adantr.mm"
include "ocvocv.mm"
include "ocvss.mm"
include "a1i.mm"
include "ocvcss.mm"
include "sylan2.mm"
include "mrcsscl.mm"
include "syl3anc.mm"
include "mrcssid.mm"
include "sylan.mm"
include "ocv2ss.mm"
include "3syl.mm"
include "wceq.mm"
include "mrccl.mm"
include "cssi.mm"
include "syl.mm"
include "sseqtr4d.mm"
include "eqssd.mm"

theorem mrccss
  let cC: class C
  let cS: class S
  let cF: class F
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  assume mrccss.v: |- V = ( Base ` W )
  assume mrccss.o: |- ._|_ = ( ocv ` W )
  assume mrccss.c: |- C = ( CSubSp ` W )
  assume mrccss.f: |- F = ( mrCls ` C )


  assert |- ( ( W e. PreHil /\ S C_ V ) -> ( F ` S ) = ( ._|_ ` ( ._|_ ` S ) ) )

  proof
    cW
    cphl
    wcel
    #
    cS
    cV
    wss
    #
    wa
    #
    cS
    cF
    cfv
    #
    cS
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @2
    cC
    cV
    cmre
    cfv
    wcel
    #
    cS
    @5
    wss
    @5
    cC
    wcel
    #
    @3
    @5
    wss
    @0
    @6
    @1
    cC
    cV
    cW
    mrccss.v
    mrccss.c
    cssmre
    #
    adantr
    cS
    c.pe
    cV
    cW
    mrccss.v
    mrccss.o
    ocvocv
    @1
    @0
    @4
    cV
    wss
    #
    @7
    @9
    @1
    cS
    c.pe
    cV
    cW
    mrccss.v
    mrccss.o
    ocvss
    a1i
    cC
    @4
    c.pe
    cV
    cW
    mrccss.v
    mrccss.c
    mrccss.o
    ocvcss
    sylan2
    cC
    cS
    cF
    @5
    cV
    mrccss.f
    mrcsscl
    syl3anc
    @2
    @5
    @3
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @3
    @2
    cS
    @3
    wss
    #
    @10
    @4
    wss
    @5
    @11
    wss
    @0
    @6
    @1
    @12
    @8
    cC
    cS
    cF
    cV
    mrccss.f
    mrcssid
    sylan
    @3
    cS
    c.pe
    cW
    mrccss.o
    ocv2ss
    @4
    @10
    c.pe
    cW
    mrccss.o
    ocv2ss
    3syl
    @2
    @3
    cC
    wcel
    #
    @3
    @11
    wceq
    @0
    @6
    @1
    @13
    @8
    cC
    cS
    cF
    cV
    mrccss.f
    mrccl
    sylan
    cC
    @3
    c.pe
    cW
    mrccss.o
    mrccss.c
    cssi
    syl
    sseqtr4d
    eqssd
end
