include "cvv.mm"
include "wcel.mm"
include "crn.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "cmpt.mm"
include "wceq.mm"
include "ccom.mm"
include "cmrex.mm"
include "cmvar.mm"
include "cpm.mm"
include "co.mm"
include "eqid.mm"
include "msubffval.mm"
include "wfn.mm"
include "cmap.mm"
include "wf.mm"
include "mrsubff.mm"
include "ffn.mm"
include "syl.mm"
include "fnfvelrn.mm"
include "sylan.mm"
include "feqmptd.mm"
include "eqidd.mm"
include "fveq1.mm"
include "opeq2d.mm"
include "mpteq2dv.mm"
include "fmptco.mm"
include "eqtr4d.mm"
include "rneqd.mm"
include "cres.mm"
include "rnco.mm"
include "wss.mm"
include "ssid.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "rneqi.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "wn.mm"
include "c0.mm"
include "mpt0.mm"
include "eqcomi.mm"
include "cmsub.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "cmrsub.mm"
include "rn0.mm"
include "mpteq1d.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem elmsubrn
  let cS: class S
  let cT: class T
  let ve: setvar e
  let vf: setvar f
  let cE: class E
  let cO: class O
  let vg: setvar g
  assume elmsubrn.e: |- E = ( mEx ` T )
  assume elmsubrn.o: |- O = ( mRSubst ` T )
  assume elmsubrn.s: |- S = ( mSubst ` T )

  disjoint e f
  disjoint E e
  disjoint E f
  disjoint O e
  disjoint O f
  disjoint T e
  disjoint e g
  disjoint f g
  disjoint E g
  disjoint O g
  disjoint T g
  assert |- ran S = ran ( f e. ran O |-> ( e e. E |-> <. ( 1st ` e ) , ( f ` ( 2nd ` e ) ) >. ) )

  proof
    cT
    cvv
    wcel
    #
    cS
    crn
    #
    vf
    cO
    crn
    #
    ve
    cE
    ve
    cv
    #
    c1st
    cfv
    #
    @3
    c2nd
    cfv
    #
    vf
    cv
    #
    cfv
    #
    cop
    #
    cmpt
    #
    cmpt
    #
    crn
    #
    wceq
    @0
    @1
    @10
    cO
    ccom
    #
    crn
    #
    @11
    @0
    cS
    @12
    @0
    cS
    vg
    cT
    cmrex
    cfv
    #
    cT
    cmvar
    cfv
    #
    cpm
    co
    #
    ve
    cE
    @4
    @5
    vg
    cv
    #
    cO
    cfv
    #
    cfv
    #
    cop
    #
    cmpt
    #
    cmpt
    @12
    @14
    cS
    cT
    ve
    vg
    cE
    cO
    @15
    cvv
    @15
    eqid
    #
    @14
    eqid
    #
    elmsubrn.s
    elmsubrn.e
    elmsubrn.o
    msubffval
    @0
    vg
    vf
    @16
    @2
    @18
    @9
    @21
    cO
    @10
    @0
    cO
    @16
    wfn
    #
    @17
    @16
    wcel
    @18
    @2
    wcel
    @0
    @16
    @14
    @14
    cmap
    co
    #
    cO
    wf
    @24
    @14
    cO
    cT
    @15
    cvv
    @22
    @23
    elmsubrn.o
    mrsubff
    #
    @16
    @25
    cO
    ffn
    syl
    @16
    @17
    cO
    fnfvelrn
    sylan
    @0
    vg
    @16
    @25
    cO
    @26
    feqmptd
    @0
    @10
    eqidd
    @6
    @18
    wceq
    #
    ve
    cE
    @8
    @20
    @27
    @7
    @19
    @4
    @5
    @6
    @18
    fveq1
    opeq2d
    mpteq2dv
    fmptco
    eqtr4d
    rneqd
    @13
    @10
    @2
    cres
    #
    crn
    @11
    @10
    cO
    rnco
    @28
    @10
    @2
    @2
    wss
    @28
    @10
    wceq
    @2
    ssid
    vf
    @2
    @2
    @9
    resmpt
    ax-mp
    rneqi
    eqtri
    syl6eq
    @0
    wn
    #
    cS
    @10
    @29
    c0
    vf
    c0
    @9
    cmpt
    #
    cS
    @10
    @30
    c0
    vf
    @9
    mpt0
    eqcomi
    @29
    cS
    cT
    cmsub
    cfv
    c0
    elmsubrn.s
    cT
    cmsub
    fvprc
    syl5eq
    @29
    vf
    @2
    c0
    @9
    @29
    @2
    c0
    crn
    c0
    @29
    cO
    c0
    @29
    cO
    cT
    cmrsub
    cfv
    c0
    elmsubrn.o
    cT
    cmrsub
    fvprc
    syl5eq
    rneqd
    rn0
    syl6eq
    mpteq1d
    3eqtr4a
    rneqd
    pm2.61i
end
