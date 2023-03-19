include "clf.mm"
include "wcel.mm"
include "ccnfn.mm"
include "cnmf.mm"
include "cfv.mm"
include "cr.mm"
include "nmcfnex.mm"
include "ex.mm"
include "cv.mm"
include "cabs.mm"
include "cno.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "chil.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "simpr.mm"
include "nmbdfnlb.mm"
include "3expa.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "oveq1.mm"
include "breq2d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "lnfncon.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem lnfncnbd
  let cT: class T
  let vx: setvar x
  let vy: setvar y


  assert |- ( T e. LinFn -> ( T e. ContFn <-> ( normfn ` T ) e. RR ) )

  proof
    cT
    clf
    wcel
    #
    cT
    ccnfn
    wcel
    #
    cT
    cnmf
    cfv
    #
    cr
    wcel
    #
    @0
    @1
    @3
    cT
    nmcfnex
    ex
    @0
    @3
    vy
    cv
    #
    cT
    cfv
    cabs
    cfv
    #
    vx
    cv
    #
    @4
    cno
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vy
    chil
    wral
    #
    vx
    cr
    wrex
    #
    @1
    @0
    @3
    @11
    @0
    @3
    wa
    #
    @3
    @5
    @2
    @7
    cmul
    co
    #
    cle
    wbr
    #
    vy
    chil
    wral
    #
    @11
    @0
    @3
    simpr
    @12
    @14
    vy
    chil
    @0
    @3
    @4
    chil
    wcel
    @14
    @4
    cT
    nmbdfnlb
    3expa
    ralrimiva
    @10
    @15
    vx
    @2
    cr
    @6
    @2
    wceq
    #
    @9
    @14
    vy
    chil
    @16
    @8
    @13
    @5
    cle
    @6
    @2
    @7
    cmul
    oveq1
    breq2d
    ralbidv
    rspcev
    syl2anc
    ex
    vx
    vy
    cT
    lnfncon
    sylibrd
    impbid
end
