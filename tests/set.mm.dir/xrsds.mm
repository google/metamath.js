include "cxrs.mm"
include "cds.mm"
include "cfv.mm"
include "cxr.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cxne.mm"
include "cxad.mm"
include "co.mm"
include "cif.mm"
include "cmpt2.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cxp.mm"
include "wf.mm"
include "wral.mm"
include "wa.mm"
include "id.mm"
include "xnegcl.mm"
include "xaddcl.mm"
include "syl2anr.mm"
include "sylan2.mm"
include "ifcld.mm"
include "rgen2a.mm"
include "eqid.mm"
include "fmpt2.mm"
include "mpbi.mm"
include "xrex.mm"
include "xpex.mm"
include "fex2.mm"
include "mp3an.mm"
include "cxmu.mm"
include "cordt.mm"
include "df-xrs.mm"
include "odrngds.mm"
include "ax-mp.mm"
include "eqtr4i.mm"

theorem xrsds
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cA: class A
  let cB: class B
  assume xrsds.d: |- D = ( dist ` RR*s )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  assert |- D = ( x e. RR* , y e. RR* |-> if ( x <_ y , ( y +e -e x ) , ( x +e -e y ) ) )

  proof
    cD
    cxrs
    cds
    cfv
    #
    vx
    vy
    cxr
    cxr
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    @2
    @1
    cxne
    #
    cxad
    co
    #
    @1
    @2
    cxne
    #
    cxad
    co
    #
    cif
    #
    cmpt2
    #
    xrsds.d
    @9
    cvv
    wcel
    #
    @9
    @0
    wceq
    cxr
    cxr
    cxp
    #
    cxr
    @9
    wf
    #
    @11
    cvv
    wcel
    cxr
    cvv
    wcel
    @10
    @8
    cxr
    wcel
    #
    vy
    cxr
    wral
    vx
    cxr
    wral
    @12
    @13
    vx
    vy
    cxr
    @1
    cxr
    wcel
    #
    @2
    cxr
    wcel
    #
    wa
    @3
    @5
    @7
    cxr
    @15
    @15
    @4
    cxr
    wcel
    @5
    cxr
    wcel
    @14
    @15
    id
    @1
    xnegcl
    @2
    @4
    xaddcl
    syl2anr
    @15
    @14
    @6
    cxr
    wcel
    @7
    cxr
    wcel
    @2
    xnegcl
    @1
    @6
    xaddcl
    sylan2
    ifcld
    rgen2a
    vx
    vy
    cxr
    cxr
    @8
    cxr
    @9
    @9
    eqid
    fmpt2
    mpbi
    cxr
    cxr
    xrex
    xrex
    xpex
    xrex
    @11
    cxr
    @9
    cvv
    cvv
    fex2
    mp3an
    cxr
    @9
    cxad
    cxmu
    cle
    cordt
    cfv
    cle
    cvv
    cxrs
    vx
    vy
    df-xrs
    odrngds
    ax-mp
    eqtr4i
end
