include "crh.mm"
include "co.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "cfv.mm"
include "cbs.mm"
include "cv.mm"
include "cmulr.mm"
include "wceq.mm"
include "wrex.mm"
include "simpl1.mm"
include "simpl2.mm"
include "eqid.mm"
include "rhmf.mm"
include "ffvelrnda.mm"
include "syl2anc.mm"
include "wral.mm"
include "simpll1.mm"
include "simpr.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "rhmmul.mm"
include "syl3anc.mm"
include "dvdsr2.mm"
include "biimpac.mm"
include "r19.29.mm"
include "simpl.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "reximi.mm"
include "syl.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "rexlimivw.mm"
include "dvdsr.mm"
include "sylanbrc.mm"

theorem rhmdvdsr
  let cA: class A
  let cB: class B
  let c.pa: class .||
  let c.dv: class ./
  let cR: class R
  let cS: class S
  let cF: class F
  let cX: class X
  let vc: setvar c
  let vy: setvar y
  assume rhmdvdsr.x: |- X = ( Base ` R )
  assume rhmdvdsr.m: |- .|| = ( ||r ` R )
  assume rhmdvdsr.n: |- ./ = ( ||r ` S )


  assert |- ( ( ( F e. ( R RingHom S ) /\ A e. X /\ B e. X ) /\ A .|| B ) -> ( F ` A ) ./ ( F ` B ) )

  proof
    cF
    cR
    cS
    crh
    co
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cA
    cB
    c.pa
    wbr
    #
    wa
    #
    cA
    cF
    cfv
    #
    cS
    cbs
    cfv
    #
    wcel
    #
    vy
    cv
    #
    @6
    cS
    cmulr
    cfv
    #
    co
    #
    cB
    cF
    cfv
    #
    wceq
    #
    vy
    @7
    wrex
    #
    @6
    @12
    c.dv
    wbr
    @5
    @0
    @1
    @8
    @0
    @1
    @2
    @4
    simpl1
    @0
    @1
    @2
    @4
    simpl2
    #
    @0
    cX
    @7
    cA
    cF
    cX
    @7
    cR
    cS
    cF
    rhmdvdsr.x
    @7
    eqid
    #
    rhmf
    #
    ffvelrnda
    syl2anc
    @5
    vc
    cv
    #
    cF
    cfv
    #
    @7
    wcel
    #
    @19
    @6
    @10
    co
    #
    @12
    wceq
    #
    wa
    #
    vc
    cX
    wrex
    #
    @14
    @5
    @20
    vc
    cX
    wral
    @22
    vc
    cX
    wrex
    #
    @24
    @5
    @20
    vc
    cX
    @5
    @18
    cX
    wcel
    #
    wa
    #
    @0
    @26
    @20
    @0
    @1
    @2
    @4
    @26
    simpll1
    #
    @5
    @26
    simpr
    #
    @0
    cX
    @7
    @18
    cF
    @17
    ffvelrnda
    syl2anc
    ralrimiva
    @5
    @18
    cA
    cR
    cmulr
    cfv
    #
    co
    #
    cF
    cfv
    #
    @21
    wceq
    #
    vc
    cX
    wral
    #
    @31
    cB
    wceq
    #
    vc
    cX
    wrex
    #
    @25
    @5
    @33
    vc
    cX
    @27
    @0
    @26
    @1
    @33
    @28
    @29
    @5
    @1
    @26
    @15
    adantr
    @18
    cA
    cR
    cS
    @30
    @10
    cF
    cX
    rhmdvdsr.x
    @30
    eqid
    #
    @10
    eqid
    #
    rhmmul
    syl3anc
    ralrimiva
    @5
    @4
    @1
    @36
    @3
    @4
    simpr
    @15
    @1
    @4
    @36
    vc
    cX
    c.pa
    cR
    @30
    cA
    cB
    rhmdvdsr.x
    rhmdvdsr.m
    @37
    dvdsr2
    biimpac
    syl2anc
    @34
    @36
    wa
    @33
    @35
    wa
    #
    vc
    cX
    wrex
    @25
    @33
    @35
    vc
    cX
    r19.29
    @39
    @22
    vc
    cX
    @39
    @32
    @21
    @12
    @33
    @35
    simpl
    @39
    @31
    cB
    cF
    @33
    @35
    simpr
    fveq2d
    eqtr3d
    reximi
    syl
    syl2anc
    @20
    @22
    vc
    cX
    r19.29
    syl2anc
    @23
    @14
    vc
    cX
    @13
    @22
    vy
    @19
    @7
    @9
    @19
    wceq
    @11
    @21
    @12
    @9
    @19
    @6
    @10
    oveq1
    eqeq1d
    rspcev
    rexlimivw
    syl
    vy
    @7
    c.dv
    cS
    @10
    @6
    @12
    @16
    rhmdvdsr.n
    @38
    dvdsr
    sylanbrc
end
