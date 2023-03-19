include "cgrp.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cc0.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cfv.mm"
include "c1.mm"
include "cabs.mm"
include "cfz.mm"
include "cn.mm"
include "simpl2.mm"
include "wn.mm"
include "simprl.mm"
include "cc.mm"
include "wb.mm"
include "simpl3.mm"
include "zcnd.mm"
include "abs00.mm"
include "necon3bbid.mm"
include "syl.mm"
include "mpbird.mm"
include "cn0.mm"
include "wo.mm"
include "nn0abscl.mm"
include "elnn0.mm"
include "sylib.mm"
include "ord.mm"
include "mt3d.mm"
include "cneg.mm"
include "simprr.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "cminusg.mm"
include "simpl1.mm"
include "eqid.mm"
include "mulgneg.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "grpinvid.mm"
include "3eqtrd.mm"
include "zred.mm"
include "absord.mm"
include "mpjaod.mm"
include "odlem2.mm"
include "elfznn.mm"

theorem odnncl
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


  assert |- ( ( ( G e. Grp /\ A e. X /\ N e. ZZ ) /\ ( N =/= 0 /\ ( N .x. A ) = .0. ) ) -> ( O ` A ) e. NN )

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
    cN
    cc0
    wne
    #
    cN
    cA
    c.x
    co
    #
    c.0
    wceq
    #
    wa
    #
    wa
    #
    cA
    cO
    cfv
    #
    c1
    cN
    cabs
    cfv
    #
    cfz
    co
    wcel
    #
    @9
    cn
    wcel
    @8
    @1
    @10
    cn
    wcel
    #
    @10
    cA
    c.x
    co
    #
    c.0
    wceq
    #
    @11
    @0
    @1
    @2
    @7
    simpl2
    #
    @8
    @12
    @10
    cc0
    wceq
    #
    @8
    @16
    wn
    #
    @4
    @3
    @4
    @6
    simprl
    @8
    cN
    cc
    wcel
    #
    @17
    @4
    wb
    @8
    cN
    @0
    @1
    @2
    @7
    simpl3
    #
    zcnd
    @18
    @16
    cN
    cc0
    cN
    abs00
    necon3bbid
    syl
    mpbird
    @8
    @12
    @16
    @8
    @10
    cn0
    wcel
    #
    @12
    @16
    wo
    @8
    @2
    @20
    @19
    cN
    nn0abscl
    syl
    @10
    elnn0
    sylib
    ord
    mt3d
    @8
    @10
    cN
    wceq
    #
    @14
    @10
    cN
    cneg
    #
    wceq
    #
    @8
    @14
    @21
    @6
    @3
    @4
    @6
    simprr
    #
    @21
    @13
    @5
    c.0
    @10
    cN
    cA
    c.x
    oveq1
    eqeq1d
    syl5ibrcom
    @8
    @14
    @23
    @22
    cA
    c.x
    co
    #
    c.0
    wceq
    @8
    @25
    @5
    cG
    cminusg
    cfv
    #
    cfv
    #
    c.0
    @26
    cfv
    #
    c.0
    @8
    @0
    @2
    @1
    @25
    @27
    wceq
    @0
    @1
    @2
    @7
    simpl1
    #
    @19
    @15
    cX
    c.x
    cG
    @26
    cN
    cA
    odcl.1
    odid.3
    @26
    eqid
    #
    mulgneg
    syl3anc
    @8
    @5
    c.0
    @26
    @24
    fveq2d
    @8
    @0
    @28
    c.0
    wceq
    @29
    cG
    @26
    c.0
    odid.4
    @30
    grpinvid
    syl
    3eqtrd
    @23
    @13
    @25
    c.0
    @10
    @22
    cA
    c.x
    oveq1
    eqeq1d
    syl5ibrcom
    @8
    cN
    @8
    cN
    @19
    zred
    absord
    mpjaod
    cA
    c.x
    cG
    @10
    cO
    cX
    c.0
    odcl.1
    odcl.2
    odid.3
    odid.4
    odlem2
    syl3anc
    @9
    @10
    elfznn
    syl
end
