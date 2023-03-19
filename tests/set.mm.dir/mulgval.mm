include "cz.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "cn.mm"
include "csn.mm"
include "cxp.mm"
include "c1.mm"
include "cseq.mm"
include "cfv.mm"
include "cneg.mm"
include "cif.mm"
include "wa.mm"
include "simpl.mm"
include "eqeq1d.mm"
include "breq2d.mm"
include "simpr.mm"
include "sneqd.mm"
include "xpeq2d.mm"
include "seqeq3d.mm"
include "syl6eqr.mm"
include "fveq12d.mm"
include "negeqd.mm"
include "fveq2d.mm"
include "ifbieq12d.mm"
include "ifbieq2d.mm"
include "mulgfval.mm"
include "c0g.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ifex.mm"
include "ovmpt2a.mm"

theorem mulgval
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let c.x: class .x.
  let cG: class G
  let cI: class I
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let vn: setvar n
  let vw: setvar w
  let vx: setvar x
  let vs: setvar s
  assume mulgval.b: |- B = ( Base ` G )
  assume mulgval.p: |- .+ = ( +g ` G )
  assume mulgval.o: |- .0. = ( 0g ` G )
  assume mulgval.i: |- I = ( invg ` G )
  assume mulgval.t: |- .x. = ( .g ` G )
  assume mulgval.s: |- S = seq 1 ( .+ , ( NN X. { X } ) )


  assert |- ( ( N e. ZZ /\ X e. B ) -> ( N .x. X ) = if ( N = 0 , .0. , if ( 0 < N , ( S ` N ) , ( I ` ( S ` -u N ) ) ) ) )

  proof
    vn
    vx
    cN
    cX
    cz
    cB
    vn
    cv
    #
    cc0
    wceq
    #
    c.0
    cc0
    @0
    clt
    wbr
    #
    @0
    c.pl
    cn
    vx
    cv
    #
    csn
    #
    cxp
    #
    c1
    cseq
    #
    cfv
    #
    @0
    cneg
    #
    @6
    cfv
    #
    cI
    cfv
    #
    cif
    #
    cif
    cN
    cc0
    wceq
    #
    c.0
    cc0
    cN
    clt
    wbr
    #
    cN
    cS
    cfv
    #
    cN
    cneg
    #
    cS
    cfv
    #
    cI
    cfv
    #
    cif
    #
    cif
    c.x
    @0
    cN
    wceq
    #
    @3
    cX
    wceq
    #
    wa
    #
    @1
    @12
    @11
    @18
    c.0
    @21
    @0
    cN
    cc0
    @19
    @20
    simpl
    #
    eqeq1d
    @21
    @2
    @13
    @7
    @10
    @14
    @17
    @21
    @0
    cN
    cc0
    clt
    @22
    breq2d
    @21
    @0
    cN
    @6
    cS
    @21
    @6
    c.pl
    cn
    cX
    csn
    #
    cxp
    #
    c1
    cseq
    cS
    @21
    @5
    @24
    c.pl
    c1
    @21
    @4
    @23
    cn
    @21
    @3
    cX
    @19
    @20
    simpr
    sneqd
    xpeq2d
    seqeq3d
    mulgval.s
    syl6eqr
    #
    @22
    fveq12d
    @21
    @9
    @16
    cI
    @21
    @8
    @15
    @6
    cS
    @25
    @21
    @0
    cN
    @22
    negeqd
    fveq12d
    fveq2d
    ifbieq12d
    ifbieq2d
    vx
    cB
    c.pl
    c.x
    vn
    cG
    cI
    c.0
    mulgval.b
    mulgval.p
    mulgval.o
    mulgval.i
    mulgval.t
    mulgfval
    @12
    c.0
    @18
    c.0
    cG
    c0g
    cfv
    cvv
    mulgval.o
    cG
    c0g
    fvex
    eqeltri
    @13
    @14
    @17
    cN
    cS
    fvex
    @16
    cI
    fvex
    ifex
    ifex
    ovmpt2a
end
