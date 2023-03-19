include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "ctsu.mm"
include "cmnd.mm"
include "wcel.mm"
include "wceq.mm"
include "ccmn.mm"
include "cmnmnd.mm"
include "syl.mm"
include "gsumz.mm"
include "syl2anc.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "cv.mm"
include "mndidcl.mm"
include "adantr.mm"
include "fmptd.mm"
include "csn.mm"
include "cxp.mm"
include "cfsupp.mm"
include "fconstmpt.mm"
include "cvv.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "fczfsuppd.mm"
include "syl5eqbrr.mm"
include "tsmsid.mm"
include "eqeltrrd.mm"

theorem tsms0
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cG: class G
  let cV: class V
  let c.0: class .0.
  assume tsms0.z: |- .0. = ( 0g ` G )
  assume tsms0.1: |- ( ph -> G e. CMnd )
  assume tsms0.2: |- ( ph -> G e. TopSp )
  assume tsms0.a: |- ( ph -> A e. V )

  disjoint A x
  disjoint G x
  disjoint ph x
  disjoint V x
  disjoint .0. x
  assert |- ( ph -> .0. e. ( G tsums ( x e. A |-> .0. ) ) )

  proof
    wph
    cG
    vx
    cA
    c.0
    cmpt
    #
    cgsu
    co
    #
    c.0
    cG
    @0
    ctsu
    co
    wph
    cG
    cmnd
    wcel
    #
    cA
    cV
    wcel
    @1
    c.0
    wceq
    wph
    cG
    ccmn
    wcel
    @2
    tsms0.1
    cG
    cmnmnd
    syl
    #
    tsms0.a
    cA
    vx
    cG
    cV
    c.0
    tsms0.z
    gsumz
    syl2anc
    wph
    cA
    cG
    cbs
    cfv
    #
    @0
    cG
    cV
    c.0
    @4
    eqid
    #
    tsms0.z
    tsms0.1
    tsms0.2
    tsms0.a
    wph
    vx
    cA
    c.0
    @4
    @0
    wph
    c.0
    @4
    wcel
    #
    vx
    cv
    cA
    wcel
    wph
    @2
    @6
    @3
    @4
    cG
    c.0
    @5
    tsms0.z
    mndidcl
    syl
    adantr
    @0
    eqid
    fmptd
    wph
    @0
    cA
    c.0
    csn
    cxp
    c.0
    cfsupp
    vx
    cA
    c.0
    fconstmpt
    wph
    cA
    cV
    cvv
    c.0
    tsms0.a
    c.0
    cvv
    wcel
    wph
    c.0
    cG
    c0g
    cfv
    cvv
    tsms0.z
    cG
    c0g
    fvex
    eqeltri
    a1i
    fczfsuppd
    syl5eqbrr
    tsmsid
    eqeltrrd
end
