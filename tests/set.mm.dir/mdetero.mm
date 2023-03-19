include "cv.mm"
include "wceq.mm"
include "co.mm"
include "cif.mm"
include "cmpt2.mm"
include "cfv.mm"
include "c0g.mm"
include "wcel.mm"
include "3adant2.mm"
include "w3a.mm"
include "crg.mm"
include "ccrg.mm"
include "crngring.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "ifcld.mm"
include "mdetrlin2.mm"
include "mdetrsca2.mm"
include "eqid.mm"
include "mdetralt2.mm"
include "oveq2d.mm"
include "ringrz.mm"
include "syl2anc.mm"
include "3eqtrd.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "cmat.mm"
include "cbs.mm"
include "wf.mm"
include "mdetf.mm"
include "matbas2d.mm"
include "ffvelrnd.mm"
include "grprid.mm"

theorem mdetero
  let wph: wff ph
  let cD: class D
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let vi: setvar i
  let vj: setvar j
  let cI: class I
  let cJ: class J
  let cK: class K
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume mdetero.d: |- D = ( N maDet R )
  assume mdetero.k: |- K = ( Base ` R )
  assume mdetero.p: |- .+ = ( +g ` R )
  assume mdetero.t: |- .x. = ( .r ` R )
  assume mdetero.r: |- ( ph -> R e. CRing )
  assume mdetero.n: |- ( ph -> N e. Fin )
  assume mdetero.x: |- ( ( ph /\ j e. N ) -> X e. K )
  assume mdetero.y: |- ( ( ph /\ j e. N ) -> Y e. K )
  assume mdetero.z: |- ( ( ph /\ i e. N /\ j e. N ) -> Z e. K )
  assume mdetero.w: |- ( ph -> W e. K )
  assume mdetero.i: |- ( ph -> I e. N )
  assume mdetero.j: |- ( ph -> J e. N )
  assume mdetero.ij: |- ( ph -> I =/= J )

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
  disjoint Y i
  disjoint W i
  disjoint W j
  disjoint .x. i
  disjoint .x. j
  disjoint .+ i
  disjoint .+ j
  assert |- ( ph -> ( D ` ( i e. N , j e. N |-> if ( i = I , ( X .+ ( W .x. Y ) ) , if ( i = J , Y , Z ) ) ) ) = ( D ` ( i e. N , j e. N |-> if ( i = I , X , if ( i = J , Y , Z ) ) ) ) )

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
    cX
    cW
    cY
    c.x
    co
    #
    c.pl
    co
    @0
    cJ
    wceq
    #
    cY
    cZ
    cif
    #
    cif
    cmpt2
    cD
    cfv
    vi
    vj
    cN
    cN
    @1
    cX
    @4
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    vi
    vj
    cN
    cN
    @1
    @2
    @4
    cif
    cmpt2
    cD
    cfv
    #
    c.pl
    co
    @7
    cR
    c0g
    cfv
    #
    c.pl
    co
    #
    @7
    wph
    cD
    c.pl
    cR
    vi
    vj
    cI
    cK
    cN
    cX
    @2
    @4
    mdetero.d
    mdetero.k
    mdetero.p
    mdetero.r
    mdetero.n
    wph
    vj
    cv
    cN
    wcel
    #
    cX
    cK
    wcel
    @0
    cN
    wcel
    #
    mdetero.x
    3adant2
    #
    wph
    @12
    @11
    w3a
    #
    cR
    crg
    wcel
    #
    cW
    cK
    wcel
    #
    cY
    cK
    wcel
    #
    @2
    cK
    wcel
    wph
    @12
    @15
    @11
    wph
    cR
    ccrg
    wcel
    #
    @15
    mdetero.r
    cR
    crngring
    syl
    #
    3ad2ant1
    wph
    @12
    @16
    @11
    mdetero.w
    3ad2ant1
    wph
    @11
    @17
    @12
    mdetero.y
    3adant2
    #
    cK
    cR
    c.x
    cW
    cY
    mdetero.k
    mdetero.t
    ringcl
    syl3anc
    @14
    @3
    cY
    cZ
    cK
    @20
    mdetero.z
    ifcld
    #
    mdetero.i
    mdetrlin2
    wph
    @8
    @9
    @7
    c.pl
    wph
    @8
    cW
    vi
    vj
    cN
    cN
    @1
    cY
    @4
    cif
    cmpt2
    cD
    cfv
    #
    c.x
    co
    cW
    @9
    c.x
    co
    #
    @9
    wph
    cD
    cR
    c.x
    vi
    vj
    cW
    cI
    cK
    cN
    cY
    @4
    mdetero.d
    mdetero.k
    mdetero.t
    mdetero.r
    mdetero.n
    @20
    @21
    mdetero.w
    mdetero.i
    mdetrsca2
    wph
    @22
    @9
    cW
    c.x
    wph
    cD
    cR
    vi
    vj
    cI
    cJ
    cK
    cN
    cY
    cZ
    @9
    mdetero.d
    mdetero.k
    @9
    eqid
    #
    mdetero.r
    mdetero.n
    mdetero.y
    mdetero.z
    mdetero.i
    mdetero.j
    mdetero.ij
    mdetralt2
    oveq2d
    wph
    @15
    @16
    @23
    @9
    wceq
    @19
    mdetero.w
    cK
    cR
    c.x
    cW
    @9
    mdetero.k
    mdetero.t
    @24
    ringrz
    syl2anc
    3eqtrd
    oveq2d
    wph
    cR
    cgrp
    wcel
    #
    @7
    cK
    wcel
    @10
    @7
    wceq
    wph
    @15
    @25
    @19
    cR
    ringgrp
    syl
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
    @6
    cD
    wph
    @18
    @27
    cK
    cD
    wf
    mdetero.r
    @26
    @27
    cD
    cR
    cK
    cN
    mdetero.d
    @26
    eqid
    #
    @27
    eqid
    #
    mdetero.k
    mdetf
    syl
    wph
    vi
    vj
    @26
    @27
    @5
    cR
    cK
    cN
    ccrg
    @28
    mdetero.k
    @29
    mdetero.n
    mdetero.r
    @14
    @1
    cX
    @4
    cK
    @13
    @21
    ifcld
    matbas2d
    ffvelrnd
    cK
    c.pl
    cR
    @7
    @9
    mdetero.k
    mdetero.p
    @24
    grprid
    syl2anc
    3eqtrd
end
