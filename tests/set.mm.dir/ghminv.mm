include "cghm.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "cplusg.mm"
include "c0g.mm"
include "cgrp.mm"
include "ghmgrp1.mm"
include "eqid.mm"
include "grprinv.mm"
include "sylan.mm"
include "fveq2d.mm"
include "grpinvcl.mm"
include "ghmlin.mm"
include "mpd3an3.mm"
include "ghmid.mm"
include "adantr.mm"
include "3eqtr3d.mm"
include "cbs.mm"
include "wb.mm"
include "ghmgrp2.mm"
include "ghmf.mm"
include "ffvelrnda.mm"
include "wf.mm"
include "ffvelrnd.mm"
include "grpinvid1.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "eqcomd.mm"

theorem ghminv
  let cB: class B
  let cS: class S
  let cT: class T
  let cF: class F
  let cM: class M
  let cN: class N
  let cX: class X
  assume ghminv.b: |- B = ( Base ` S )
  assume ghminv.y: |- M = ( invg ` S )
  assume ghminv.z: |- N = ( invg ` T )


  assert |- ( ( F e. ( S GrpHom T ) /\ X e. B ) -> ( F ` ( M ` X ) ) = ( N ` ( F ` X ) ) )

  proof
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cX
    cF
    cfv
    #
    cN
    cfv
    #
    cX
    cM
    cfv
    #
    cF
    cfv
    #
    @2
    @4
    @6
    wceq
    #
    @3
    @6
    cT
    cplusg
    cfv
    #
    co
    #
    cT
    c0g
    cfv
    #
    wceq
    #
    @2
    cX
    @5
    cS
    cplusg
    cfv
    #
    co
    #
    cF
    cfv
    #
    cS
    c0g
    cfv
    #
    cF
    cfv
    #
    @9
    @10
    @2
    @13
    @15
    cF
    @0
    cS
    cgrp
    wcel
    #
    @1
    @13
    @15
    wceq
    cS
    cT
    cF
    ghmgrp1
    #
    cB
    @12
    cS
    cM
    cX
    @15
    ghminv.b
    @12
    eqid
    #
    @15
    eqid
    #
    ghminv.y
    grprinv
    sylan
    fveq2d
    @0
    @1
    @5
    cB
    wcel
    #
    @14
    @9
    wceq
    @0
    @17
    @1
    @21
    @18
    cB
    cS
    cM
    cX
    ghminv.b
    ghminv.y
    grpinvcl
    sylan
    #
    @12
    @8
    cS
    cT
    cX
    cF
    @5
    cB
    ghminv.b
    @19
    @8
    eqid
    #
    ghmlin
    mpd3an3
    @0
    @16
    @10
    wceq
    @1
    cS
    cT
    cF
    @15
    @10
    @20
    @10
    eqid
    #
    ghmid
    adantr
    3eqtr3d
    @2
    cT
    cgrp
    wcel
    #
    @3
    cT
    cbs
    cfv
    #
    wcel
    @6
    @26
    wcel
    @7
    @11
    wb
    @0
    @25
    @1
    cS
    cT
    cF
    ghmgrp2
    adantr
    @0
    cB
    @26
    cX
    cF
    cS
    cT
    cF
    cB
    @26
    ghminv.b
    @26
    eqid
    #
    ghmf
    #
    ffvelrnda
    @2
    cB
    @26
    @5
    cF
    @0
    cB
    @26
    cF
    wf
    @1
    @28
    adantr
    @22
    ffvelrnd
    @26
    @8
    cT
    cN
    @3
    @6
    @10
    @27
    @23
    @24
    ghminv.z
    grpinvid1
    syl3anc
    mpbird
    eqcomd
end
