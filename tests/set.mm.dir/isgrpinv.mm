include "cgrp.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "crio.mm"
include "grpinvval.mm"
include "ad2antlr.mm"
include "simpr.mm"
include "wreu.mm"
include "wb.mm"
include "simpllr.mm"
include "simplr.mm"
include "ffvelrnd.mm"
include "simplll.mm"
include "grpinveu.mm"
include "syl2anc.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "riota2.mm"
include "mpbid.mm"
include "eqtrd.mm"
include "ex.mm"
include "ralimdva.mm"
include "impr.mm"
include "wfn.mm"
include "grpinvfn.mm"
include "ffn.mm"
include "ad2antrl.mm"
include "eqfnfv.mm"
include "sylancr.mm"
include "mpbird.mm"
include "grpinvf.mm"
include "grplinv.mm"
include "ralrimiva.mm"
include "jca.mm"
include "feq1.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "syl5ibcom.mm"
include "impbid.mm"

theorem isgrpinv
  let vx: setvar x
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cM: class M
  let cN: class N
  let c.0: class .0.
  let ve: setvar e
  let vy: setvar y
  let vz: setvar z
  let cX: class X
  assume grpinv.b: |- B = ( Base ` G )
  assume grpinv.p: |- .+ = ( +g ` G )
  assume grpinv.u: |- .0. = ( 0g ` G )
  assume grpinv.n: |- N = ( invg ` G )

  disjoint B x
  disjoint G x
  disjoint .0. x
  disjoint .+ x
  disjoint M x
  disjoint N x
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint B e
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint G e
  disjoint G y
  disjoint G z
  disjoint .0. e
  disjoint .0. y
  disjoint .0. z
  disjoint .+ e
  disjoint .+ y
  disjoint .+ z
  disjoint M e
  disjoint N y
  disjoint N z
  disjoint X y
  disjoint X z
  assert |- ( G e. Grp -> ( ( M : B --> B /\ A. x e. B ( ( M ` x ) .+ x ) = .0. ) <-> N = M ) )

  proof
    cG
    cgrp
    wcel
    #
    cB
    cB
    cM
    wf
    #
    vx
    cv
    #
    cM
    cfv
    #
    @2
    c.pl
    co
    #
    c.0
    wceq
    #
    vx
    cB
    wral
    #
    wa
    #
    cN
    cM
    wceq
    #
    @0
    @7
    @8
    @0
    @7
    wa
    #
    @8
    @2
    cN
    cfv
    #
    @3
    wceq
    #
    vx
    cB
    wral
    #
    @0
    @1
    @6
    @12
    @0
    @1
    wa
    #
    @5
    @11
    vx
    cB
    @13
    @2
    cB
    wcel
    #
    wa
    #
    @5
    @11
    @15
    @5
    wa
    #
    @10
    ve
    cv
    #
    @2
    c.pl
    co
    #
    c.0
    wceq
    #
    ve
    cB
    crio
    #
    @3
    @14
    @10
    @20
    wceq
    @13
    @5
    ve
    cB
    c.pl
    cG
    cN
    @2
    c.0
    grpinv.b
    grpinv.p
    grpinv.u
    grpinv.n
    grpinvval
    ad2antlr
    @16
    @5
    @20
    @3
    wceq
    #
    @15
    @5
    simpr
    @16
    @3
    cB
    wcel
    @19
    ve
    cB
    wreu
    #
    @5
    @21
    wb
    @16
    cB
    cB
    @2
    cM
    @0
    @1
    @14
    @5
    simpllr
    @13
    @14
    @5
    simplr
    #
    ffvelrnd
    @16
    @0
    @14
    @22
    @0
    @1
    @14
    @5
    simplll
    @23
    ve
    cB
    c.pl
    cG
    @2
    c.0
    grpinv.b
    grpinv.p
    grpinv.u
    grpinveu
    syl2anc
    @19
    @5
    ve
    cB
    @3
    @17
    @3
    wceq
    @18
    @4
    c.0
    @17
    @3
    @2
    c.pl
    oveq1
    eqeq1d
    riota2
    syl2anc
    mpbid
    eqtrd
    ex
    ralimdva
    impr
    @9
    cN
    cB
    wfn
    cM
    cB
    wfn
    #
    @8
    @12
    wb
    cB
    cG
    cN
    grpinv.b
    grpinv.n
    grpinvfn
    @1
    @24
    @0
    @6
    cB
    cB
    cM
    ffn
    ad2antrl
    vx
    cB
    cN
    cM
    eqfnfv
    sylancr
    mpbird
    ex
    @0
    cB
    cB
    cN
    wf
    #
    @10
    @2
    c.pl
    co
    #
    c.0
    wceq
    #
    vx
    cB
    wral
    #
    wa
    @8
    @7
    @0
    @25
    @28
    cB
    cG
    cN
    grpinv.b
    grpinv.n
    grpinvf
    @0
    @27
    vx
    cB
    cB
    c.pl
    cG
    cN
    @2
    c.0
    grpinv.b
    grpinv.p
    grpinv.u
    grpinv.n
    grplinv
    ralrimiva
    jca
    @8
    @25
    @1
    @28
    @6
    cB
    cB
    cN
    cM
    feq1
    @8
    @27
    @5
    vx
    cB
    @8
    @26
    @4
    c.0
    @8
    @10
    @3
    @2
    c.pl
    @2
    cN
    cM
    fveq1
    oveq1d
    eqeq1d
    ralbidv
    anbi12d
    syl5ibcom
    impbid
end
