include "cc.mm"
include "wss.mm"
include "cr.mm"
include "cv.mm"
include "clog.mm"
include "cfv.mm"
include "cim.mm"
include "cmpt.mm"
include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "cmnf.mm"
include "cc0.mm"
include "cioc.mm"
include "cdif.mm"
include "difss.mm"
include "eqsstri.mm"
include "ax-resscn.mm"
include "crp.mm"
include "cabs.mm"
include "cif.mm"
include "c1.mm"
include "caddc.mm"
include "cdiv.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "eqid.mm"
include "wi.mm"
include "ellogdm.mm"
include "simplbi.mm"
include "logdmn0.mm"
include "logcld.mm"
include "imcld.mm"
include "fmpti.mm"
include "wa.mm"
include "simpl.mm"
include "simpr.mm"
include "logcnlem2.mm"
include "cmin.mm"
include "clt.mm"
include "simpll.mm"
include "simprl.mm"
include "simplr.mm"
include "simprr.mm"
include "logcnlem4.mm"
include "expr.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "fvex.mm"
include "fvmpt.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "oveq12d.mm"
include "breq1d.mm"
include "sylibrd.mm"
include "elcncf1ii.mm"
include "mp2an.mm"

theorem logcnlem5
  let vx: setvar x
  let cD: class D
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume logcn.d: |- D = ( CC \ ( -oo (,] 0 ) )

  disjoint D x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint D w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint D y
  disjoint D z
  assert |- ( x e. D |-> ( Im ` ( log ` x ) ) ) e. ( D -cn-> RR )

  proof
    cD
    cc
    wss
    cr
    cc
    wss
    vx
    cD
    vx
    cv
    #
    clog
    cfv
    #
    cim
    cfv
    #
    cmpt
    #
    cD
    cr
    ccncf
    co
    wcel
    cD
    cc
    cmnf
    cc0
    cioc
    co
    #
    cdif
    cc
    logcn.d
    cc
    @4
    difss
    eqsstri
    ax-resscn
    vy
    vz
    vw
    cD
    cr
    @3
    vy
    cv
    #
    crp
    wcel
    @5
    @5
    cim
    cfv
    cabs
    cfv
    cif
    #
    @5
    cabs
    cfv
    vz
    cv
    #
    c1
    @7
    caddc
    co
    cdiv
    co
    cmul
    co
    #
    cle
    wbr
    @6
    @8
    cif
    #
    vx
    cD
    cr
    @2
    @3
    @3
    eqid
    #
    @0
    cD
    wcel
    #
    @1
    @11
    @0
    @11
    @0
    cc
    wcel
    @0
    cr
    wcel
    @0
    crp
    wcel
    wi
    @0
    cD
    logcn.d
    ellogdm
    simplbi
    @0
    cD
    logcn.d
    logdmn0
    logcld
    imcld
    fmpti
    @5
    cD
    wcel
    #
    @7
    crp
    wcel
    #
    wa
    @5
    cD
    @7
    @6
    @8
    logcn.d
    @6
    eqid
    #
    @8
    eqid
    #
    @12
    @13
    simpl
    @12
    @13
    simpr
    logcnlem2
    @12
    vw
    cv
    #
    cD
    wcel
    #
    wa
    #
    @13
    wa
    #
    @5
    @16
    cmin
    co
    cabs
    cfv
    @9
    clt
    wbr
    #
    @5
    clog
    cfv
    #
    cim
    cfv
    #
    @16
    clog
    cfv
    #
    cim
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @7
    clt
    wbr
    #
    @5
    @3
    cfv
    #
    @16
    @3
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @7
    clt
    wbr
    @18
    @13
    @20
    @27
    @18
    @13
    @20
    wa
    #
    wa
    @5
    @16
    cD
    @7
    @6
    @8
    logcn.d
    @14
    @15
    @12
    @17
    @32
    simpll
    @18
    @13
    @20
    simprl
    @12
    @17
    @32
    simplr
    @18
    @13
    @20
    simprr
    logcnlem4
    expr
    @19
    @31
    @26
    @7
    clt
    @19
    @30
    @25
    cabs
    @19
    @28
    @22
    @29
    @24
    cmin
    @12
    @28
    @22
    wceq
    @17
    @13
    vx
    @5
    @2
    @22
    cD
    @3
    @0
    @5
    wceq
    @1
    @21
    cim
    @0
    @5
    clog
    fveq2
    fveq2d
    @10
    @21
    cim
    fvex
    fvmpt
    ad2antrr
    @17
    @29
    @24
    wceq
    @12
    @13
    vx
    @16
    @2
    @24
    cD
    @3
    @0
    @16
    wceq
    @1
    @23
    cim
    @0
    @16
    clog
    fveq2
    fveq2d
    @10
    @23
    cim
    fvex
    fvmpt
    ad2antlr
    oveq12d
    fveq2d
    breq1d
    sylibrd
    elcncf1ii
    mp2an
end
