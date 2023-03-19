include "chl.mm"
include "wcel.mm"
include "ccld.mm"
include "cfv.mm"
include "w3a.mm"
include "co.mm"
include "wss.mm"
include "clmod.mm"
include "cphl.mm"
include "hlphl.mm"
include "3ad2ant1.mm"
include "phllmod.mm"
include "syl.mm"
include "simp2.mm"
include "lssss.mm"
include "3ad2ant2.mm"
include "ocvlss.mm"
include "syl2anc.mm"
include "lsmcl.mm"
include "syl3anc.mm"
include "cv.mm"
include "wa.mm"
include "cplusg.mm"
include "cip.mm"
include "csg.mm"
include "cnm.mm"
include "eqid.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpr.mm"
include "simpl3.mm"
include "pjthlem2.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem pjth
  let c.po: class .(+)
  let cU: class U
  let cJ: class J
  let cL: class L
  let cO: class O
  let cV: class V
  let cW: class W
  let vx: setvar x
  assume pjth.v: |- V = ( Base ` W )
  assume pjth.s: |- .(+) = ( LSSum ` W )
  assume pjth.o: |- O = ( ocv ` W )
  assume pjth.j: |- J = ( TopOpen ` W )
  assume pjth.l: |- L = ( LSubSp ` W )


  assert |- ( ( W e. CHil /\ U e. L /\ U e. ( Clsd ` J ) ) -> ( U .(+) ( O ` U ) ) = V )

  proof
    cW
    chl
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
    w3a
    #
    cU
    cU
    cO
    cfv
    #
    c.po
    co
    #
    cV
    @3
    @5
    cL
    wcel
    #
    @5
    cV
    wss
    @3
    cW
    clmod
    wcel
    #
    @1
    @4
    cL
    wcel
    #
    @6
    @3
    cW
    cphl
    wcel
    #
    @7
    @0
    @1
    @9
    @2
    cW
    hlphl
    3ad2ant1
    #
    cW
    phllmod
    syl
    @0
    @1
    @2
    simp2
    @3
    @9
    cU
    cV
    wss
    #
    @8
    @10
    @1
    @0
    @11
    @2
    cL
    cU
    cV
    cW
    pjth.v
    pjth.l
    lssss
    3ad2ant2
    cU
    cL
    cO
    cV
    cW
    pjth.v
    pjth.o
    pjth.l
    ocvlss
    syl2anc
    c.po
    cL
    cU
    @4
    cW
    pjth.l
    pjth.s
    lsmcl
    syl3anc
    cL
    @5
    cV
    cW
    pjth.v
    pjth.l
    lssss
    syl
    @3
    vx
    cV
    @5
    @3
    vx
    cv
    #
    cV
    wcel
    #
    @12
    @5
    wcel
    @3
    @13
    wa
    @12
    cW
    cplusg
    cfv
    #
    c.po
    cU
    cW
    cip
    cfv
    #
    cJ
    cL
    cW
    csg
    cfv
    #
    cW
    cnm
    cfv
    #
    cO
    cV
    cW
    pjth.v
    @17
    eqid
    @14
    eqid
    @16
    eqid
    @15
    eqid
    pjth.l
    @0
    @1
    @2
    @13
    simpl1
    @0
    @1
    @2
    @13
    simpl2
    @3
    @13
    simpr
    pjth.j
    pjth.s
    pjth.o
    @0
    @1
    @2
    @13
    simpl3
    pjthlem2
    ex
    ssrdv
    eqssd
end
