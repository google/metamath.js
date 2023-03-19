include "cgrp.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cfv.mm"
include "cn.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "cdiv.mm"
include "cfl.mm"
include "cmul.mm"
include "cmin.mm"
include "csg.mm"
include "cr.mm"
include "crp.mm"
include "wceq.mm"
include "simpl3.mm"
include "zred.mm"
include "simpr.mm"
include "nnrpd.mm"
include "modval.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "simpl1.mm"
include "nnzd.mm"
include "nndivred.mm"
include "flcld.mm"
include "zmulcld.mm"
include "simpl2.mm"
include "eqid.mm"
include "mulgsubdir.mm"
include "syl13anc.mm"
include "cc.mm"
include "nncn.mm"
include "zcn.mm"
include "mulcom.mm"
include "syl2an.mm"
include "mulgass.mm"
include "odid.mm"
include "syl.mm"
include "oveq2d.mm"
include "mulgz.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "mulgcl.mm"
include "syl3anc.mm"
include "grpsubid1.mm"

theorem odmod
  let cA: class A
  let c.x: class .x.
  let cG: class G
  let cN: class N
  let cO: class O
  let cX: class X
  let c.0: class .0.
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vx: setvar x
  assume odcl.1: |- X = ( Base ` G )
  assume odcl.2: |- O = ( od ` G )
  assume odid.3: |- .x. = ( .g ` G )
  assume odid.4: |- .0. = ( 0g ` G )


  assert |- ( ( ( G e. Grp /\ A e. X /\ N e. ZZ ) /\ ( O ` A ) e. NN ) -> ( ( N mod ( O ` A ) ) .x. A ) = ( N .x. A ) )

  proof
    cG
    cgrp
    wcel
    #
    cA
    cX
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    #
    cA
    cO
    cfv
    #
    cn
    wcel
    #
    wa
    #
    cN
    @4
    cmo
    co
    #
    cA
    c.x
    co
    cN
    @4
    cN
    @4
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    cA
    c.x
    co
    #
    cN
    cA
    c.x
    co
    #
    @10
    cA
    c.x
    co
    #
    cG
    csg
    cfv
    #
    co
    #
    @13
    @6
    @7
    @11
    cA
    c.x
    @6
    cN
    cr
    wcel
    @4
    crp
    wcel
    @7
    @11
    wceq
    @6
    cN
    @0
    @1
    @2
    @5
    simpl3
    #
    zred
    #
    @6
    @4
    @3
    @5
    simpr
    #
    nnrpd
    cN
    @4
    modval
    syl2anc
    oveq1d
    @6
    @0
    @2
    @10
    cz
    wcel
    @1
    @12
    @16
    wceq
    @0
    @1
    @2
    @5
    simpl1
    #
    @17
    @6
    @4
    @9
    @6
    @4
    @19
    nnzd
    #
    @6
    @8
    @6
    cN
    @4
    @18
    @19
    nndivred
    flcld
    #
    zmulcld
    @0
    @1
    @2
    @5
    simpl2
    #
    cX
    c.x
    cG
    cN
    @15
    @10
    cA
    odcl.1
    odid.3
    @15
    eqid
    #
    mulgsubdir
    syl13anc
    @6
    @16
    @13
    c.0
    @15
    co
    #
    @13
    @6
    @14
    c.0
    @13
    @15
    @6
    @14
    @9
    @4
    cmul
    co
    #
    cA
    c.x
    co
    #
    @9
    @4
    cA
    c.x
    co
    #
    c.x
    co
    #
    c.0
    @6
    @10
    @26
    cA
    c.x
    @6
    @5
    @9
    cz
    wcel
    #
    @10
    @26
    wceq
    #
    @19
    @22
    @5
    @4
    cc
    wcel
    @9
    cc
    wcel
    @31
    @30
    @4
    nncn
    @9
    zcn
    @4
    @9
    mulcom
    syl2an
    syl2anc
    oveq1d
    @6
    @0
    @30
    @4
    cz
    wcel
    @1
    @27
    @29
    wceq
    @20
    @22
    @21
    @23
    cX
    c.x
    cG
    @9
    @4
    cA
    odcl.1
    odid.3
    mulgass
    syl13anc
    @6
    @29
    @9
    c.0
    c.x
    co
    #
    c.0
    @6
    @28
    c.0
    @9
    c.x
    @6
    @1
    @28
    c.0
    wceq
    @23
    cA
    c.x
    cG
    cO
    cX
    c.0
    odcl.1
    odcl.2
    odid.3
    odid.4
    odid
    syl
    oveq2d
    @6
    @0
    @30
    @32
    c.0
    wceq
    @20
    @22
    cX
    c.x
    cG
    @9
    c.0
    odcl.1
    odid.3
    odid.4
    mulgz
    syl2anc
    eqtrd
    3eqtrd
    oveq2d
    @6
    @0
    @13
    cX
    wcel
    #
    @25
    @13
    wceq
    @20
    @6
    @0
    @2
    @1
    @33
    @20
    @17
    @23
    cX
    c.x
    cG
    cN
    cA
    odcl.1
    odid.3
    mulgcl
    syl3anc
    cX
    cG
    @15
    @13
    c.0
    odcl.1
    odid.4
    @24
    grpsubid1
    syl2anc
    eqtrd
    3eqtrd
end
