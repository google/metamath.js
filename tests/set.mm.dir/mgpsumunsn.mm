include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "cun.mm"
include "wcel.mm"
include "wceq.mm"
include "difsnid.mm"
include "syl.mm"
include "eqcomd.mm"
include "mpteq1d.mm"
include "oveq2d.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "ccrg.mm"
include "ccmn.mm"
include "crngmgp.mm"
include "cfn.mm"
include "diffi.mm"
include "cv.mm"
include "eldifi.mm"
include "sylan2.mm"
include "neldifsnd.mm"
include "gsumunsn.mm"
include "eqtrd.mm"

theorem mgpsumunsn
  let wph: wff ph
  let cA: class A
  let cR: class R
  let c.x: class .x.
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
  assume mgpsumunsn.x: |- ( ph -> X e. ( Base ` R ) )
  assume mgpsumunsn.e: |- ( k = I -> A = X )

  disjoint I k
  disjoint M k
  disjoint N k
  disjoint R k
  disjoint k ph
  disjoint X k
  disjoint k x
  assert |- ( ph -> ( M gsum ( k e. N |-> A ) ) = ( ( M gsum ( k e. ( N \ { I } ) |-> A ) ) .x. X ) )

  proof
    wph
    cM
    vk
    cN
    cA
    cmpt
    #
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
    @1
    cun
    #
    cA
    cmpt
    #
    cgsu
    co
    cM
    vk
    @2
    cA
    cmpt
    cgsu
    co
    cX
    c.x
    co
    wph
    @0
    @4
    cM
    cgsu
    wph
    vk
    cN
    @3
    cA
    wph
    @3
    cN
    wph
    cI
    cN
    wcel
    @3
    cN
    wceq
    mgpsumunsn.i
    cN
    cI
    difsnid
    syl
    eqcomd
    mpteq1d
    oveq2d
    wph
    @2
    cR
    cbs
    cfv
    #
    c.x
    vk
    cM
    cI
    cN
    cA
    cX
    @5
    cR
    cM
    mgpsumunsn.m
    @5
    eqid
    mgpbas
    cR
    c.x
    cM
    mgpsumunsn.m
    mgpsumunsn.t
    mgpplusg
    wph
    cR
    ccrg
    wcel
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
    @2
    cfn
    wcel
    mgpsumunsn.n
    cN
    @1
    diffi
    syl
    vk
    cv
    #
    @2
    wcel
    wph
    @6
    cN
    wcel
    cA
    @5
    wcel
    @6
    cN
    @1
    eldifi
    mgpsumunsn.a
    sylan2
    mgpsumunsn.i
    wph
    cI
    cN
    neldifsnd
    mgpsumunsn.x
    mgpsumunsn.e
    gsumunsn
    eqtrd
end
