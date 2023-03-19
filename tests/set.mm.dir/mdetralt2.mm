include "cmat.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt2.mm"
include "eqid.mm"
include "ccrg.mm"
include "wcel.mm"
include "w3a.mm"
include "3adant2.mm"
include "ifcld.mm"
include "matbas2d.mm"
include "wa.mm"
include "csb.mm"
include "eqidd.mm"
include "weq.mm"
include "iftrue.mm"
include "ad2antrl.mm"
include "csbeq1a.mm"
include "ad2antll.mm"
include "eqtrd.mm"
include "adantr.mm"
include "simpr.mm"
include "wi.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "nfcv.mm"
include "ovmpt2dxf.mm"
include "ifeq2d.mm"
include "ifid.mm"
include "syl6eq.mm"
include "eqtr4d.mm"
include "ralrimiva.mm"
include "mdetralt.mm"

theorem mdetralt2
  let wph: wff ph
  let cD: class D
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let cI: class I
  let cJ: class J
  let cK: class K
  let cN: class N
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vw: setvar w
  assume mdetralt2.d: |- D = ( N maDet R )
  assume mdetralt2.k: |- K = ( Base ` R )
  assume mdetralt2.z: |- .0. = ( 0g ` R )
  assume mdetralt2.r: |- ( ph -> R e. CRing )
  assume mdetralt2.n: |- ( ph -> N e. Fin )
  assume mdetralt2.x: |- ( ( ph /\ j e. N ) -> X e. K )
  assume mdetralt2.y: |- ( ( ph /\ i e. N /\ j e. N ) -> Y e. K )
  assume mdetralt2.i: |- ( ph -> I e. N )
  assume mdetralt2.j: |- ( ph -> J e. N )
  assume mdetralt2.ij: |- ( ph -> I =/= J )

  disjoint i ph
  disjoint j ph
  disjoint i j
  disjoint K i
  disjoint K j
  disjoint N i
  disjoint N j
  disjoint I i
  disjoint I j
  disjoint J i
  disjoint J j
  disjoint X i
  disjoint ph w
  disjoint i w
  disjoint j w
  disjoint K w
  disjoint N w
  disjoint I w
  disjoint J w
  disjoint X w
  disjoint Y w
  assert |- ( ph -> ( D ` ( i e. N , j e. N |-> if ( i = I , X , if ( i = J , X , Y ) ) ) ) = .0. )

  proof
    wph
    cN
    cR
    cmat
    co
    #
    @0
    cbs
    cfv
    #
    cD
    cR
    cI
    cJ
    cN
    vi
    vj
    cN
    cN
    vi
    cv
    #
    cI
    wceq
    #
    cX
    @2
    cJ
    wceq
    #
    cX
    cY
    cif
    #
    cif
    #
    cmpt2
    #
    c.0
    vw
    mdetralt2.d
    @0
    eqid
    #
    @1
    eqid
    #
    mdetralt2.z
    mdetralt2.r
    wph
    vi
    vj
    @0
    @1
    @6
    cR
    cK
    cN
    ccrg
    @8
    mdetralt2.k
    @9
    mdetralt2.n
    mdetralt2.r
    wph
    @2
    cN
    wcel
    #
    vj
    cv
    #
    cN
    wcel
    #
    w3a
    #
    @3
    cX
    @5
    cK
    wph
    @12
    cX
    cK
    wcel
    #
    @10
    mdetralt2.x
    3adant2
    #
    @13
    @4
    cX
    cY
    cK
    @15
    mdetralt2.y
    ifcld
    ifcld
    matbas2d
    mdetralt2.i
    mdetralt2.j
    mdetralt2.ij
    wph
    cI
    vw
    cv
    #
    @7
    co
    #
    cJ
    @16
    @7
    co
    #
    wceq
    vw
    cN
    wph
    @16
    cN
    wcel
    #
    wa
    #
    @17
    vj
    @16
    cX
    csb
    #
    @18
    @20
    vi
    vj
    cI
    @16
    cN
    cN
    @6
    @21
    @7
    cN
    cK
    @20
    @7
    eqidd
    #
    @20
    @3
    vj
    vw
    weq
    #
    wa
    wa
    @6
    cX
    @21
    @3
    @6
    cX
    wceq
    #
    @20
    @23
    @3
    cX
    @5
    iftrue
    ad2antrl
    @23
    cX
    @21
    wceq
    #
    @20
    @3
    vj
    @16
    cX
    csbeq1a
    #
    ad2antll
    eqtrd
    @20
    @3
    wa
    cN
    eqidd
    wph
    cI
    cN
    wcel
    @19
    mdetralt2.i
    adantr
    wph
    @19
    simpr
    #
    wph
    @12
    wa
    #
    @14
    wi
    @20
    @21
    cK
    wcel
    #
    wi
    vj
    vw
    @20
    @29
    vj
    @20
    vj
    nfv
    #
    vj
    @21
    cK
    vj
    @16
    cX
    nfcsb1v
    #
    nfel1
    nfim
    @23
    @28
    @20
    @14
    @29
    @23
    @12
    @19
    wph
    @11
    @16
    cN
    eleq1
    anbi2d
    @23
    cX
    @21
    cK
    @26
    eleq1d
    imbi12d
    mdetralt2.x
    chvar
    #
    @20
    vi
    nfv
    #
    @30
    vj
    cI
    nfcv
    vi
    @16
    nfcv
    #
    vi
    @21
    nfcv
    #
    @31
    ovmpt2dxf
    @20
    vi
    vj
    cJ
    @16
    cN
    cN
    @6
    @21
    @7
    cN
    cK
    @22
    @20
    @4
    @23
    wa
    wa
    @6
    cX
    @21
    @4
    @24
    @20
    @23
    @4
    @6
    @3
    cX
    cX
    cif
    cX
    @4
    @3
    @5
    cX
    cX
    @4
    cX
    cY
    iftrue
    ifeq2d
    @3
    cX
    ifid
    syl6eq
    ad2antrl
    @23
    @25
    @20
    @4
    @26
    ad2antll
    eqtrd
    @20
    @4
    wa
    cN
    eqidd
    wph
    cJ
    cN
    wcel
    @19
    mdetralt2.j
    adantr
    @27
    @32
    @33
    @30
    vj
    cJ
    nfcv
    @34
    @35
    @31
    ovmpt2dxf
    eqtr4d
    ralrimiva
    mdetralt
end
