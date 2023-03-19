include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "crg.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "ccrg.mm"
include "crngring.mm"
include "syl.mm"
include "eqid.mm"
include "ringidcl.mm"
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
include "ringridm.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem mgpsumn
  let wph: wff ph
  let cA: class A
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  let vk: setvar k
  let cI: class I
  let cM: class M
  let cN: class N
  let cX: class X
  let vx: setvar x
  assume mgpsumunsn.m: |- M = ( mulGrp ` R )
  assume mgpsumunsn.t: |- .x. = ( .r ` R )
  assume mgpsumunsn.r: |- ( ph -> R e. CRing )
  assume mgpsumunsn.n: |- ( ph -> N e. Fin )
  assume mgpsumunsn.i: |- ( ph -> I e. N )
  assume mgpsumunsn.a: |- ( ( ph /\ k e. N ) -> A e. ( Base ` R ) )
  assume mgpsumn.n: |- .1. = ( 1r ` R )
  assume mgpsumn.1: |- ( k = I -> A = .1. )

  disjoint .1. k
  disjoint I k
  disjoint M k
  disjoint N k
  disjoint R k
  disjoint k ph
  disjoint X k
  disjoint k x
  assert |- ( ph -> ( M gsum ( k e. N |-> A ) ) = ( M gsum ( k e. ( N \ { I } ) |-> A ) ) )

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
    c.1
    c.x
    co
    #
    @2
    wph
    cA
    cR
    c.x
    vk
    cI
    cM
    cN
    c.1
    mgpsumunsn.m
    mgpsumunsn.t
    mgpsumunsn.r
    mgpsumunsn.n
    mgpsumunsn.i
    mgpsumunsn.a
    wph
    cR
    crg
    wcel
    #
    c.1
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
    cR
    crngring
    syl
    #
    @5
    cR
    c.1
    @5
    eqid
    #
    mgpsumn.n
    ringidcl
    syl
    mgpsumn.1
    mgpsumunsn
    wph
    @4
    @2
    @5
    wcel
    @3
    @2
    wceq
    @7
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
    @8
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
    @10
    cN
    wcel
    @9
    @10
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
    c.1
    @2
    @8
    mgpsumunsn.t
    mgpsumn.n
    ringridm
    syl2anc
    eqtrd
end
