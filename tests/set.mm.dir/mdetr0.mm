include "cv.mm"
include "wceq.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "cif.mm"
include "cmpt2.mm"
include "eqid.mm"
include "wcel.mm"
include "crg.mm"
include "ccrg.mm"
include "crngring.mm"
include "syl.mm"
include "ring0cl.mm"
include "3ad2ant1.mm"
include "mdetrsca2.mm"
include "ringlz.mm"
include "syl2anc.mm"
include "ifeq1d.mm"
include "mpt2eq3dv.mm"
include "fveq2d.mm"
include "cmat.mm"
include "cbs.mm"
include "wf.mm"
include "mdetf.mm"
include "w3a.mm"
include "ifcld.mm"
include "matbas2d.mm"
include "ffvelrnd.mm"
include "3eqtr3d.mm"

theorem mdetr0
  let wph: wff ph
  let cD: class D
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let cI: class I
  let cK: class K
  let cN: class N
  let cX: class X
  let c.0: class .0.
  assume mdetr0.d: |- D = ( N maDet R )
  assume mdetr0.k: |- K = ( Base ` R )
  assume mdetr0.z: |- .0. = ( 0g ` R )
  assume mdetr0.r: |- ( ph -> R e. CRing )
  assume mdetr0.n: |- ( ph -> N e. Fin )
  assume mdetr0.x: |- ( ( ph /\ i e. N /\ j e. N ) -> X e. K )
  assume mdetr0.i: |- ( ph -> I e. N )

  disjoint i ph
  disjoint j ph
  disjoint i j
  disjoint K i
  disjoint K j
  disjoint N i
  disjoint N j
  disjoint I i
  disjoint I j
  disjoint .0. i
  disjoint .0. j
  disjoint R i
  disjoint R j
  assert |- ( ph -> ( D ` ( i e. N , j e. N |-> if ( i = I , .0. , X ) ) ) = .0. )

  proof
    wph
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
    c.0
    c.0
    cR
    cmulr
    cfv
    #
    co
    #
    cX
    cif
    #
    cmpt2
    #
    cD
    cfv
    c.0
    vi
    vj
    cN
    cN
    @1
    c.0
    cX
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    @2
    co
    #
    @8
    c.0
    wph
    cD
    cR
    @2
    vi
    vj
    c.0
    cI
    cK
    cN
    c.0
    cX
    mdetr0.d
    mdetr0.k
    @2
    eqid
    #
    mdetr0.r
    mdetr0.n
    wph
    @0
    cN
    wcel
    #
    c.0
    cK
    wcel
    #
    vj
    cv
    cN
    wcel
    #
    wph
    cR
    crg
    wcel
    #
    @12
    wph
    cR
    ccrg
    wcel
    #
    @14
    mdetr0.r
    cR
    crngring
    syl
    #
    cK
    cR
    c.0
    mdetr0.k
    mdetr0.z
    ring0cl
    syl
    #
    3ad2ant1
    #
    mdetr0.x
    @17
    mdetr0.i
    mdetrsca2
    wph
    @5
    @7
    cD
    wph
    vi
    vj
    cN
    cN
    @4
    @6
    wph
    @1
    @3
    c.0
    cX
    wph
    @14
    @12
    @3
    c.0
    wceq
    @16
    @17
    cK
    cR
    @2
    c.0
    c.0
    mdetr0.k
    @10
    mdetr0.z
    ringlz
    syl2anc
    ifeq1d
    mpt2eq3dv
    fveq2d
    wph
    @14
    @8
    cK
    wcel
    @9
    c.0
    wceq
    @16
    wph
    cN
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    cK
    @7
    cD
    wph
    @15
    @20
    cK
    cD
    wf
    mdetr0.r
    @19
    @20
    cD
    cR
    cK
    cN
    mdetr0.d
    @19
    eqid
    #
    @20
    eqid
    #
    mdetr0.k
    mdetf
    syl
    wph
    vi
    vj
    @19
    @20
    @6
    cR
    cK
    cN
    ccrg
    @21
    mdetr0.k
    @22
    mdetr0.n
    mdetr0.r
    wph
    @11
    @13
    w3a
    @1
    c.0
    cX
    cK
    @18
    mdetr0.x
    ifcld
    matbas2d
    ffvelrnd
    cK
    cR
    @2
    @8
    c.0
    mdetr0.k
    @10
    mdetr0.z
    ringlz
    syl2anc
    3eqtr3d
end
