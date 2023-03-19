include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "cmnd.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "ccrg.mm"
include "crg.mm"
include "crngring.mm"
include "ringmnd.mm"
include "syl.mm"
include "eqid.mm"
include "mndidcl.mm"
include "mgpsumunsn.mm"
include "wceq.mm"
include "mgpbas.mm"
include "ccmn.mm"
include "crngmgp.mm"
include "cfn.mm"
include "diffi.mm"
include "cv.mm"
include "eldifi.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "gsummptcl.mm"
include "ringrz.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem mgpsumz
  let wph: wff ph
  let cA: class A
  let cR: class R
  let c.x: class .x.
  let vk: setvar k
  let cI: class I
  let cM: class M
  let cN: class N
  let c.0: class .0.
  let cX: class X
  let vx: setvar x
  assume mgpsumunsn.m: |- M = ( mulGrp ` R )
  assume mgpsumunsn.t: |- .x. = ( .r ` R )
  assume mgpsumunsn.r: |- ( ph -> R e. CRing )
  assume mgpsumunsn.n: |- ( ph -> N e. Fin )
  assume mgpsumunsn.i: |- ( ph -> I e. N )
  assume mgpsumunsn.a: |- ( ( ph /\ k e. N ) -> A e. ( Base ` R ) )
  assume mgpsumz.z: |- .0. = ( 0g ` R )
  assume mgpsumz.0: |- ( k = I -> A = .0. )

  disjoint .0. k
  disjoint I k
  disjoint M k
  disjoint N k
  disjoint R k
  disjoint k ph
  disjoint X k
  disjoint k x
  assert |- ( ph -> ( M gsum ( k e. N |-> A ) ) = .0. )

  proof
    wph
    cM
    vk
    cN
    cA
    cmpt
    cgsu
    co
    cM
    vk
    cN
    cI
    csn
    #
    cdif
    #
    cA
    cmpt
    cgsu
    co
    #
    c.0
    c.x
    co
    #
    c.0
    wph
    cA
    cR
    c.x
    vk
    cI
    cM
    cN
    c.0
    mgpsumunsn.m
    mgpsumunsn.t
    mgpsumunsn.r
    mgpsumunsn.n
    mgpsumunsn.i
    mgpsumunsn.a
    wph
    cR
    cmnd
    wcel
    #
    c.0
    cR
    cbs
    cfv
    #
    wcel
    wph
    cR
    ccrg
    wcel
    #
    @4
    mgpsumunsn.r
    @6
    cR
    crg
    wcel
    #
    @4
    cR
    crngring
    #
    cR
    ringmnd
    syl
    syl
    @5
    cR
    c.0
    @5
    eqid
    #
    mgpsumz.z
    mndidcl
    syl
    mgpsumz.0
    mgpsumunsn
    wph
    @7
    @2
    @5
    wcel
    @3
    c.0
    wceq
    wph
    @6
    @7
    mgpsumunsn.r
    @8
    syl
    wph
    @5
    vk
    cM
    @1
    cA
    @5
    cR
    cM
    mgpsumunsn.m
    @9
    mgpbas
    wph
    @6
    cM
    ccmn
    wcel
    mgpsumunsn.r
    cR
    cM
    mgpsumunsn.m
    crngmgp
    syl
    wph
    cN
    cfn
    wcel
    @1
    cfn
    wcel
    mgpsumunsn.n
    cN
    @0
    diffi
    syl
    wph
    cA
    @5
    wcel
    #
    vk
    @1
    vk
    cv
    #
    @1
    wcel
    wph
    @11
    cN
    wcel
    @10
    @11
    cN
    @0
    eldifi
    mgpsumunsn.a
    sylan2
    ralrimiva
    gsummptcl
    @5
    cR
    c.x
    @2
    c.0
    @9
    mgpsumunsn.t
    mgpsumz.z
    ringrz
    syl2anc
    eqtrd
end
