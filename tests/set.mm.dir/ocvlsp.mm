include "cphl.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "clmod.mm"
include "phllmod.mm"
include "lspssid.mm"
include "sylan.mm"
include "ocv2ss.mm"
include "syl.mm"
include "ocvss.mm"
include "a1i.mm"
include "ocvocv.mm"
include "syldan.mm"
include "clss.mm"
include "adantr.mm"
include "eqid.mm"
include "ocvlss.mm"
include "lspssp.mm"
include "syl3anc.mm"
include "sstrd.mm"
include "eqssd.mm"

theorem ocvlsp
  let cS: class S
  let cN: class N
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  assume ocvlsp.v: |- V = ( Base ` W )
  assume ocvlsp.o: |- ._|_ = ( ocv ` W )
  assume ocvlsp.n: |- N = ( LSpan ` W )


  assert |- ( ( W e. PreHil /\ S C_ V ) -> ( ._|_ ` ( N ` S ) ) = ( ._|_ ` S ) )

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
    cN
    cfv
    #
    c.pe
    cfv
    #
    cS
    c.pe
    cfv
    #
    @2
    cS
    @3
    wss
    #
    @4
    @5
    wss
    @0
    cW
    clmod
    wcel
    #
    @1
    @6
    cW
    phllmod
    #
    cS
    cN
    cV
    cW
    ocvlsp.v
    ocvlsp.n
    lspssid
    sylan
    @3
    cS
    c.pe
    cW
    ocvlsp.o
    ocv2ss
    syl
    @2
    @5
    @5
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @4
    @0
    @1
    @5
    cV
    wss
    #
    @5
    @10
    wss
    @11
    @2
    cS
    c.pe
    cV
    cW
    ocvlsp.v
    ocvlsp.o
    ocvss
    a1i
    #
    @5
    c.pe
    cV
    cW
    ocvlsp.v
    ocvlsp.o
    ocvocv
    syldan
    @2
    @3
    @9
    wss
    #
    @10
    @4
    wss
    @2
    @7
    @9
    cW
    clss
    cfv
    #
    wcel
    #
    cS
    @9
    wss
    @13
    @0
    @7
    @1
    @8
    adantr
    @0
    @1
    @11
    @15
    @12
    @5
    @14
    c.pe
    cV
    cW
    ocvlsp.v
    ocvlsp.o
    @14
    eqid
    #
    ocvlss
    syldan
    cS
    c.pe
    cV
    cW
    ocvlsp.v
    ocvlsp.o
    ocvocv
    @14
    cS
    @9
    cN
    cW
    @16
    ocvlsp.n
    lspssp
    syl3anc
    @9
    @3
    c.pe
    cW
    ocvlsp.o
    ocv2ss
    syl
    sstrd
    eqssd
end
