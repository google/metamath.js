include "cmg.mm"
include "cfv.mm"
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
include "cneg.mm"
include "cif.mm"
include "cmpt2.mm"
include "cvv.mm"
include "wcel.mm"
include "cbs.mm"
include "c0g.mm"
include "cplusg.mm"
include "cminusg.mm"
include "csb.mm"
include "eqidd.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "seqex.mm"
include "a1i.mm"
include "wa.mm"
include "id.mm"
include "seqeq2d.mm"
include "sylan9eqr.mm"
include "fveq1d.mm"
include "simpl.mm"
include "fveq2d.mm"
include "fveq12d.mm"
include "ifeq12d.mm"
include "csbied.mm"
include "mpt2eq123dv.mm"
include "df-mulg.mm"
include "zex.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "wfn.mm"
include "eqid.mm"
include "ifex.mm"
include "fnmpt2i.mm"
include "syl5eq.mm"
include "xpeq2d.mm"
include "xp0.mm"
include "syl6eq.mm"
include "fneq2d.mm"
include "mpbii.mm"
include "fn0.mm"
include "sylib.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem mulgfval
  let vx: setvar x
  let cB: class B
  let c.pl: class .+
  let c.x: class .x.
  let vn: setvar n
  let cG: class G
  let cI: class I
  let c.0: class .0.
  let vw: setvar w
  let vs: setvar s
  let cN: class N
  let cS: class S
  let cX: class X
  assume mulgval.b: |- B = ( Base ` G )
  assume mulgval.p: |- .+ = ( +g ` G )
  assume mulgval.o: |- .0. = ( 0g ` G )
  assume mulgval.i: |- I = ( invg ` G )
  assume mulgval.t: |- .x. = ( .g ` G )

  disjoint n x
  disjoint .0. n
  disjoint .0. x
  disjoint G n
  disjoint G x
  disjoint I n
  disjoint I x
  disjoint B n
  disjoint B x
  disjoint n w
  disjoint w x
  disjoint .0. w
  disjoint n s
  disjoint s w
  disjoint s x
  disjoint G s
  disjoint G w
  disjoint I s
  disjoint I w
  disjoint N n
  disjoint N x
  disjoint S n
  disjoint S x
  disjoint .+ s
  disjoint .+ w
  disjoint B w
  disjoint X n
  disjoint X x
  assert |- .x. = ( n e. ZZ , x e. B |-> if ( n = 0 , .0. , if ( 0 < n , ( seq 1 ( .+ , ( NN X. { x } ) ) ` n ) , ( I ` ( seq 1 ( .+ , ( NN X. { x } ) ) ` -u n ) ) ) ) )

  proof
    c.x
    cG
    cmg
    cfv
    #
    vn
    vx
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
    @1
    clt
    wbr
    #
    @1
    c.pl
    cn
    vx
    cv
    csn
    cxp
    #
    c1
    cseq
    #
    cfv
    #
    @1
    cneg
    #
    @5
    cfv
    #
    cI
    cfv
    #
    cif
    #
    cif
    #
    cmpt2
    #
    mulgval.t
    cG
    cvv
    wcel
    #
    @0
    @12
    wceq
    vw
    cG
    vn
    vx
    cz
    vw
    cv
    #
    cbs
    cfv
    #
    @2
    @14
    c0g
    cfv
    #
    vs
    @14
    cplusg
    cfv
    #
    @4
    c1
    cseq
    #
    @3
    @1
    vs
    cv
    #
    cfv
    #
    @7
    @19
    cfv
    #
    @14
    cminusg
    cfv
    #
    cfv
    #
    cif
    #
    csb
    #
    cif
    #
    cmpt2
    @12
    cvv
    cmg
    @14
    cG
    wceq
    #
    vn
    vx
    cz
    @15
    @26
    cz
    cB
    @11
    @27
    cz
    eqidd
    @27
    @15
    cG
    cbs
    cfv
    #
    cB
    @14
    cG
    cbs
    fveq2
    mulgval.b
    syl6eqr
    @27
    @2
    @16
    c.0
    @25
    @10
    @27
    @16
    cG
    c0g
    cfv
    #
    c.0
    @14
    cG
    c0g
    fveq2
    mulgval.o
    syl6eqr
    @27
    vs
    @18
    @24
    @10
    cvv
    @18
    cvv
    wcel
    @27
    @17
    @4
    c1
    seqex
    a1i
    @27
    @19
    @18
    wceq
    #
    wa
    #
    @3
    @20
    @6
    @23
    @9
    @31
    @1
    @19
    @5
    @30
    @27
    @19
    @18
    @5
    @30
    id
    @27
    @17
    c.pl
    @4
    c1
    @27
    @17
    cG
    cplusg
    cfv
    c.pl
    @14
    cG
    cplusg
    fveq2
    mulgval.p
    syl6eqr
    seqeq2d
    sylan9eqr
    #
    fveq1d
    @31
    @21
    @8
    @22
    cI
    @31
    @22
    cG
    cminusg
    cfv
    cI
    @31
    @14
    cG
    cminusg
    @27
    @30
    simpl
    fveq2d
    mulgval.i
    syl6eqr
    @31
    @7
    @19
    @5
    @32
    fveq1d
    fveq12d
    ifeq12d
    csbied
    ifeq12d
    mpt2eq123dv
    vx
    vw
    vn
    vs
    df-mulg
    vn
    vx
    cz
    cB
    @11
    zex
    cB
    @28
    cvv
    mulgval.b
    cG
    cbs
    fvex
    eqeltri
    mpt2ex
    fvmpt
    @13
    wn
    #
    @0
    c0
    @12
    cG
    cmg
    fvprc
    @33
    @12
    c0
    wfn
    #
    @12
    c0
    wceq
    @33
    @12
    cz
    cB
    cxp
    #
    wfn
    @34
    vn
    vx
    cz
    cB
    @11
    @12
    @12
    eqid
    @2
    c.0
    @10
    c.0
    @29
    cvv
    mulgval.o
    cG
    c0g
    fvex
    eqeltri
    @3
    @6
    @9
    @1
    @5
    fvex
    @8
    cI
    fvex
    ifex
    ifex
    fnmpt2i
    @33
    @35
    c0
    @12
    @33
    @35
    cz
    c0
    cxp
    c0
    @33
    cB
    c0
    cz
    @33
    cB
    @28
    c0
    mulgval.b
    cG
    cbs
    fvprc
    syl5eq
    xpeq2d
    cz
    xp0
    syl6eq
    fneq2d
    mpbii
    @12
    fn0
    sylib
    eqtr4d
    pm2.61i
    eqtri
end
