include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "wf1o.mm"
include "cab.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cnx.mm"
include "cop.mm"
include "cplusg.mm"
include "ccom.mm"
include "cmpt2.mm"
include "cts.mm"
include "cpw.mm"
include "csn.mm"
include "cxp.mm"
include "cpt.mm"
include "ctp.mm"
include "cmap.mm"
include "co.mm"
include "wss.mm"
include "wf.mm"
include "f1of.mm"
include "wb.mm"
include "elmapg.mm"
include "anidms.mm"
include "syl5ibr.mm"
include "abssdv.mm"
include "ovex.mm"
include "ssexg.mm"
include "sylancl.mm"
include "eqid.mm"
include "topgrpbas.mm"
include "syl.mm"
include "symgval.mm"
include "fveq2d.mm"
include "eqtr4d.mm"
include "wn.mm"
include "c0.mm"
include "base0.mm"
include "cdm.mm"
include "f1odm.mm"
include "vex.mm"
include "dmex.mm"
include "syl6eqelr.mm"
include "con3i.mm"
include "pm2.21d.mm"
include "ss0.mm"
include "csymg.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"
include "eqtr4i.mm"

theorem symgbas
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cV: class V
  assume symgbas.1: |- G = ( SymGrp ` A )
  assume symgbas.2: |- B = ( Base ` G )

  disjoint A x
  disjoint f g
  disjoint f x
  disjoint A f
  disjoint g x
  disjoint A g
  disjoint F x
  disjoint V x
  assert |- B = { x | x : A -1-1-onto-> A }

  proof
    cB
    cG
    cbs
    cfv
    #
    cA
    cA
    vx
    cv
    #
    wf1o
    #
    vx
    cab
    #
    symgbas.2
    cA
    cvv
    wcel
    #
    @3
    @0
    wceq
    @4
    @3
    cnx
    cbs
    cfv
    @3
    cop
    cnx
    cplusg
    cfv
    vf
    vg
    @3
    @3
    vf
    cv
    vg
    cv
    ccom
    cmpt2
    #
    cop
    cnx
    cts
    cfv
    cA
    cA
    cpw
    csn
    cxp
    cpt
    cfv
    #
    cop
    ctp
    #
    cbs
    cfv
    #
    @0
    @4
    @3
    cvv
    wcel
    #
    @3
    @8
    wceq
    @4
    @3
    cA
    cA
    cmap
    co
    #
    wss
    @10
    cvv
    wcel
    @9
    @4
    @2
    vx
    @10
    @2
    @1
    @10
    wcel
    #
    @4
    cA
    cA
    @1
    wf
    #
    cA
    cA
    @1
    f1of
    @4
    @11
    @12
    wb
    cA
    cA
    @1
    cvv
    cvv
    elmapg
    anidms
    syl5ibr
    abssdv
    cA
    cA
    cmap
    ovex
    @3
    @10
    cvv
    ssexg
    sylancl
    @3
    @5
    @6
    @7
    cvv
    @7
    eqid
    topgrpbas
    syl
    @4
    cG
    @7
    cbs
    vx
    cA
    @3
    @5
    vf
    vg
    cG
    @6
    cvv
    symgbas.1
    @3
    eqid
    @5
    eqid
    @6
    eqid
    symgval
    fveq2d
    eqtr4d
    @4
    wn
    #
    c0
    c0
    cbs
    cfv
    @3
    @0
    base0
    @13
    @3
    c0
    wss
    @3
    c0
    wceq
    @13
    @2
    vx
    c0
    @13
    @2
    @1
    c0
    wcel
    @2
    @4
    @2
    cA
    @1
    cdm
    cvv
    cA
    cA
    @1
    f1odm
    @1
    vx
    vex
    dmex
    syl6eqelr
    con3i
    pm2.21d
    abssdv
    @3
    ss0
    syl
    @13
    cG
    c0
    cbs
    @13
    cG
    cA
    csymg
    cfv
    c0
    symgbas.1
    cA
    csymg
    fvprc
    syl5eq
    fveq2d
    3eqtr4a
    pm2.61i
    eqtr4i
end
