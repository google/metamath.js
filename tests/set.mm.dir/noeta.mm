include "cv.mm"
include "cslt.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "crio.mm"
include "cdm.mm"
include "c2o.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "wcel.mm"
include "csuc.mm"
include "cres.mm"
include "wceq.mm"
include "wi.mm"
include "wa.mm"
include "cab.mm"
include "cfv.mm"
include "w3a.mm"
include "cio.mm"
include "cmpt.mm"
include "cif.mm"
include "cbday.mm"
include "cima.mm"
include "cuni.mm"
include "cdif.mm"
include "c1o.mm"
include "cxp.mm"
include "weq.mm"
include "eleq1.mm"
include "suceq.mm"
include "reseq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "3anbi123d.mm"
include "rexbidv.mm"
include "iotabidv.mm"
include "cbvmptv.mm"
include "ifeq2.mm"
include "ax-mp.mm"
include "eqid.mm"
include "noetalem5.mm"

theorem noeta
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A d
  disjoint A e
  disjoint A f
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint d e
  disjoint d f
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint e f
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint f x
  disjoint f y
  disjoint f z
  assert |- ( ( ( A C_ No /\ A e. V ) /\ ( B C_ No /\ B e. W ) /\ A. x e. A A. y e. B x <s y ) -> E. z e. No ( A. x e. A x <s z /\ A. y e. B z <s y /\ ( bday ` z ) C_ suc U. ( bday " ( A u. B ) ) ) )

  proof
    va
    vb
    vz
    ve
    vd
    cA
    cB
    va
    cv
    #
    vb
    cv
    #
    cslt
    wbr
    wn
    vb
    cA
    wral
    #
    va
    cA
    wrex
    #
    @2
    va
    cA
    crio
    #
    @4
    cdm
    c2o
    cop
    csn
    cun
    #
    vf
    @1
    vd
    cv
    #
    cdm
    #
    wcel
    ve
    cv
    #
    @6
    cslt
    wbr
    wn
    #
    @6
    @1
    csuc
    #
    cres
    @8
    @10
    cres
    wceq
    wi
    ve
    cA
    wral
    wa
    vd
    cA
    wrex
    vb
    cab
    #
    vf
    cv
    #
    @7
    wcel
    #
    @9
    @6
    @12
    csuc
    #
    cres
    #
    @8
    @14
    cres
    #
    wceq
    #
    wi
    #
    ve
    cA
    wral
    #
    @12
    @6
    cfv
    #
    @0
    wceq
    #
    w3a
    #
    vd
    cA
    wrex
    #
    va
    cio
    #
    cmpt
    #
    cif
    #
    vc
    cV
    cW
    @26
    cbday
    cB
    cima
    cuni
    csuc
    @26
    cdm
    cdif
    c1o
    csn
    cxp
    cun
    #
    vx
    vy
    @25
    vc
    @11
    vc
    cv
    #
    @7
    wcel
    #
    @9
    @6
    @28
    csuc
    #
    cres
    #
    @8
    @30
    cres
    #
    wceq
    #
    wi
    #
    ve
    cA
    wral
    #
    @28
    @6
    cfv
    #
    @0
    wceq
    #
    w3a
    #
    vd
    cA
    wrex
    #
    va
    cio
    #
    cmpt
    #
    wceq
    @26
    @3
    @5
    @41
    cif
    wceq
    vf
    vc
    @11
    @24
    @40
    vf
    vc
    weq
    #
    @23
    @39
    va
    @42
    @22
    @38
    vd
    cA
    @42
    @13
    @29
    @19
    @35
    @21
    @37
    @12
    @28
    @7
    eleq1
    @42
    @18
    @34
    ve
    cA
    @42
    @17
    @33
    @9
    @42
    @15
    @31
    @16
    @32
    @42
    @14
    @30
    @6
    @12
    @28
    suceq
    #
    reseq2d
    @42
    @14
    @30
    @8
    @43
    reseq2d
    eqeq12d
    imbi2d
    ralbidv
    @42
    @20
    @36
    @0
    @12
    @28
    @6
    fveq2
    eqeq1d
    3anbi123d
    rexbidv
    iotabidv
    cbvmptv
    @3
    @25
    @41
    @5
    ifeq2
    ax-mp
    @27
    eqid
    noetalem5
end
