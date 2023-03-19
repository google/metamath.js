include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "cv.mm"
include "wrex.mm"
include "wn.mm"
include "wceq.mm"
include "wral.mm"
include "ralnex.mm"
include "nne.mm"
include "ralbii.mm"
include "bitr3i.mm"
include "cn0v.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "wfn.mm"
include "wa.mm"
include "fveq2.mm"
include "cba.mm"
include "eqid.mm"
include "lno0.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "ralimdv.mm"
include "wf.mm"
include "lnof.mm"
include "ffn.mm"
include "syl.mm"
include "jctild.mm"
include "fconstfv.mm"
include "fvex.mm"
include "fconst2.mm"
include "syl6ib.mm"
include "0ofval.mm"
include "3adant3.mm"
include "eqeq2d.mm"
include "sylibrd.mm"
include "syl5bi.mm"
include "necon1ad.mm"
include "imp.mm"

theorem lnon0
  let vx: setvar x
  let cT: class T
  let cU: class U
  let cL: class L
  let cO: class O
  let cW: class W
  let cX: class X
  let cZ: class Z
  assume lnon0.1: |- X = ( BaseSet ` U )
  assume lnon0.6: |- Z = ( 0vec ` U )
  assume lnon0.0: |- O = ( U 0op W )
  assume lnon0.7: |- L = ( U LnOp W )

  disjoint L x
  disjoint T x
  disjoint U x
  disjoint W x
  disjoint X x
  assert |- ( ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. L ) /\ T =/= O ) -> E. x e. X x =/= Z )

  proof
    cU
    cnv
    wcel
    #
    cW
    cnv
    wcel
    #
    cT
    cL
    wcel
    #
    w3a
    #
    cT
    cO
    wne
    vx
    cv
    #
    cZ
    wne
    #
    vx
    cX
    wrex
    #
    @3
    @6
    cT
    cO
    @6
    wn
    #
    @4
    cZ
    wceq
    #
    vx
    cX
    wral
    #
    @3
    cT
    cO
    wceq
    #
    @7
    @5
    wn
    #
    vx
    cX
    wral
    @9
    @5
    vx
    cX
    ralnex
    @11
    @8
    vx
    cX
    @4
    cZ
    nne
    ralbii
    bitr3i
    @3
    @9
    cT
    cX
    cW
    cn0v
    cfv
    #
    csn
    #
    cxp
    #
    wceq
    #
    @10
    @3
    @9
    cT
    cX
    wfn
    #
    @4
    cT
    cfv
    #
    @12
    wceq
    #
    vx
    cX
    wral
    #
    wa
    #
    @15
    @3
    @9
    @19
    @16
    @3
    @8
    @18
    vx
    cX
    @3
    @8
    @18
    @8
    @3
    @17
    cZ
    cT
    cfv
    @12
    @4
    cZ
    cT
    fveq2
    cZ
    cT
    cU
    cL
    cW
    cX
    cW
    cba
    cfv
    #
    @12
    lnon0.1
    @21
    eqid
    #
    lnon0.6
    @12
    eqid
    #
    lnon0.7
    lno0
    sylan9eqr
    ex
    ralimdv
    @3
    cX
    @21
    cT
    wf
    @16
    cT
    cU
    cL
    cW
    cX
    @21
    lnon0.1
    @22
    lnon0.7
    lnof
    cX
    @21
    cT
    ffn
    syl
    jctild
    @20
    cX
    @13
    cT
    wf
    @15
    vx
    cX
    @12
    cT
    fconstfv
    cX
    @12
    cT
    cW
    cn0v
    fvex
    fconst2
    bitr3i
    syl6ib
    @3
    cO
    @14
    cT
    @0
    @1
    cO
    @14
    wceq
    @2
    cU
    cO
    cW
    cX
    @12
    lnon0.1
    @23
    lnon0.0
    0ofval
    3adant3
    eqeq2d
    sylibrd
    syl5bi
    necon1ad
    imp
end
