include "ctop.mm"
include "wcel.mm"
include "cpw.mm"
include "cfv.mm"
include "wfn.mm"
include "cv.mm"
include "cin.mm"
include "cuni.mm"
include "cmpt.mm"
include "cvv.mm"
include "wral.mm"
include "vpwex.mm"
include "inex2.mm"
include "uniex.mm"
include "rgenw.mm"
include "nfcv.mm"
include "fnmptf.mm"
include "mp1i.mm"
include "cnt.mm"
include "ntrfval.mm"
include "syl5eq.mm"
include "fneq1d.mm"
include "mpbird.mm"
include "cmap.mm"
include "co.mm"
include "wf1o.mm"
include "wf.mm"
include "topopn.mm"
include "dssmapf1od.mm"
include "f1of.mm"
include "syl.mm"
include "clselmap.mm"
include "ffvelrnd.mm"
include "elmapfn.mm"
include "wa.mm"
include "cdif.mm"
include "ccl.mm"
include "wss.mm"
include "wceq.mm"
include "elpwi.mm"
include "ntrval2.mm"
include "sylan2.mm"
include "fveq1i.mm"
include "difeq2i.mm"
include "3eqtr4g.mm"
include "adantr.mm"
include "eqid.mm"
include "simpr.mm"
include "dssmapfv3d.mm"
include "eqtr4d.mm"
include "eqfnfvd.mm"

theorem dssmapntrcls
  let cD: class D
  let vf: setvar f
  let cI: class I
  let cJ: class J
  let cK: class K
  let cO: class O
  let cX: class X
  let vs: setvar s
  let vb: setvar b
  let vt: setvar t
  assume dssmapclsntr.x: |- X = U. J
  assume dssmapclsntr.k: |- K = ( cls ` J )
  assume dssmapclsntr.i: |- I = ( int ` J )
  assume dssmapclsntr.o: |- O = ( b e. _V |-> ( f e. ( ~P b ^m ~P b ) |-> ( s e. ~P b |-> ( b \ ( f ` ( b \ s ) ) ) ) ) )
  assume dssmapclsntr.d: |- D = ( O ` X )

  disjoint J b
  disjoint J f
  disjoint J s
  disjoint b f
  disjoint b s
  disjoint f s
  disjoint K f
  disjoint K s
  disjoint X b
  disjoint X f
  disjoint X s
  disjoint D t
  disjoint I t
  disjoint J t
  disjoint b t
  disjoint f t
  disjoint s t
  disjoint K t
  disjoint X t
  assert |- ( J e. Top -> I = ( D ` K ) )

  proof
    cJ
    ctop
    wcel
    #
    vt
    cX
    cpw
    #
    cI
    cK
    cD
    cfv
    #
    @0
    cI
    @1
    wfn
    vt
    @1
    cJ
    vt
    cv
    #
    cpw
    #
    cin
    #
    cuni
    #
    cmpt
    #
    @1
    wfn
    #
    @6
    cvv
    wcel
    #
    vt
    @1
    wral
    @8
    @0
    @9
    vt
    @1
    @5
    @4
    cJ
    vt
    vpwex
    inex2
    uniex
    rgenw
    vt
    @1
    @6
    cvv
    vt
    @1
    nfcv
    fnmptf
    mp1i
    @0
    @1
    cI
    @7
    @0
    cI
    cJ
    cnt
    cfv
    #
    @7
    dssmapclsntr.i
    vt
    cJ
    cX
    dssmapclsntr.x
    ntrfval
    syl5eq
    fneq1d
    mpbird
    @0
    @2
    @1
    @1
    cmap
    co
    #
    wcel
    @2
    @1
    wfn
    @0
    @11
    @11
    cK
    cD
    @0
    @11
    @11
    cD
    wf1o
    @11
    @11
    cD
    wf
    @0
    cX
    cD
    vf
    cO
    cJ
    vs
    vb
    dssmapclsntr.o
    dssmapclsntr.d
    cJ
    cX
    dssmapclsntr.x
    topopn
    #
    dssmapf1od
    @11
    @11
    cD
    f1of
    syl
    cJ
    cK
    cX
    dssmapclsntr.x
    dssmapclsntr.k
    clselmap
    #
    ffvelrnd
    @2
    @1
    @1
    elmapfn
    syl
    @0
    @3
    @1
    wcel
    #
    wa
    #
    @3
    cI
    cfv
    #
    cX
    cX
    @3
    cdif
    #
    cK
    cfv
    #
    cdif
    #
    @3
    @2
    cfv
    #
    @15
    @3
    @10
    cfv
    #
    cX
    @17
    cJ
    ccl
    cfv
    #
    cfv
    #
    cdif
    #
    @16
    @19
    @14
    @0
    @3
    cX
    wss
    @21
    @24
    wceq
    @3
    cX
    elpwi
    @3
    cJ
    cX
    dssmapclsntr.x
    ntrval2
    sylan2
    @3
    cI
    @10
    dssmapclsntr.i
    fveq1i
    @18
    @23
    cX
    @17
    cK
    @22
    dssmapclsntr.k
    fveq1i
    difeq2i
    3eqtr4g
    @15
    cX
    cD
    @3
    @20
    vf
    cK
    @2
    cO
    cJ
    vs
    vb
    dssmapclsntr.o
    dssmapclsntr.d
    @0
    cX
    cJ
    wcel
    @14
    @12
    adantr
    @0
    cK
    @11
    wcel
    @14
    @13
    adantr
    @2
    eqid
    @0
    @14
    simpr
    @20
    eqid
    dssmapfv3d
    eqtr4d
    eqfnfvd
end
