include "cgrp.mm"
include "wcel.mm"
include "cfn.mm"
include "cfv.mm"
include "cn.mm"
include "wa.mm"
include "wn.mm"
include "cc0.mm"
include "wceq.mm"
include "cn0.mm"
include "wo.mm"
include "odcl.mm"
include "adantl.mm"
include "elnn0.mm"
include "sylib.mm"
include "ord.mm"
include "w3a.mm"
include "cz.mm"
include "cv.mm"
include "cmg.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "eqid.mm"
include "odinf.mm"
include "wf1.mm"
include "wf.mm"
include "wss.mm"
include "wi.mm"
include "odf1.mm"
include "biimp3a.mm"
include "f1f.mm"
include "frn.mm"
include "ssfi.mm"
include "expcom.mm"
include "4syl.mm"
include "mtod.mm"
include "3expia.mm"
include "syld.mm"
include "con4d.mm"
include "3impia.mm"
include "3com23.mm"

theorem odcl2
  let cA: class A
  let cG: class G
  let cO: class O
  let cX: class X
  let vx: setvar x
  assume odcl2.1: |- X = ( Base ` G )
  assume odcl2.2: |- O = ( od ` G )


  assert |- ( ( G e. Grp /\ X e. Fin /\ A e. X ) -> ( O ` A ) e. NN )

  proof
    cG
    cgrp
    wcel
    #
    cA
    cX
    wcel
    #
    cX
    cfn
    wcel
    #
    cA
    cO
    cfv
    #
    cn
    wcel
    #
    @0
    @1
    @2
    @4
    @0
    @1
    wa
    #
    @4
    @2
    @5
    @4
    wn
    @3
    cc0
    wceq
    #
    @2
    wn
    #
    @5
    @4
    @6
    @5
    @3
    cn0
    wcel
    #
    @4
    @6
    wo
    @1
    @8
    @0
    cA
    cG
    cO
    cX
    odcl2.1
    odcl2.2
    odcl
    adantl
    @3
    elnn0
    sylib
    ord
    @0
    @1
    @6
    @7
    @0
    @1
    @6
    w3a
    #
    @2
    vx
    cz
    vx
    cv
    cA
    cG
    cmg
    cfv
    #
    co
    cmpt
    #
    crn
    #
    cfn
    wcel
    #
    vx
    cA
    @10
    @11
    cG
    cO
    cX
    odcl2.1
    odcl2.2
    @10
    eqid
    #
    @11
    eqid
    #
    odinf
    @9
    cz
    cX
    @11
    wf1
    #
    cz
    cX
    @11
    wf
    @12
    cX
    wss
    #
    @2
    @13
    wi
    @0
    @1
    @6
    @16
    vx
    cA
    @10
    @11
    cG
    cO
    cX
    odcl2.1
    odcl2.2
    @14
    @15
    odf1
    biimp3a
    cz
    cX
    @11
    f1f
    cz
    cX
    @11
    frn
    @2
    @17
    @13
    cX
    @12
    ssfi
    expcom
    4syl
    mtod
    3expia
    syld
    con4d
    3impia
    3com23
end
