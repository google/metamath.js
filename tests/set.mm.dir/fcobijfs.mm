include "cv.mm"
include "cid.mm"
include "cres.mm"
include "ccom.mm"
include "cmpt.mm"
include "wf1o.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "breq1.mm"
include "cbvrabv.mm"
include "eqtr4i.mm"
include "f1oi.mm"
include "a1i.mm"
include "wcel.mm"
include "cvv.mm"
include "elex.mm"
include "syl.mm"
include "mapfien.mm"
include "wceq.mm"
include "wb.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseli.mm"
include "wa.mm"
include "coass.mm"
include "wf.mm"
include "f1of.mm"
include "elmapi.mm"
include "fco.mm"
include "syl2an.mm"
include "fcoi1.mm"
include "syl5eqr.mm"
include "sylan2.mm"
include "mpteq2dva.mm"
include "f1oeq1.mm"
include "mpbid.mm"

theorem fcobijfs
  let wph: wff ph
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cG: class G
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume fcobij.1: |- ( ph -> G : S -1-1-onto-> T )
  assume fcobij.2: |- ( ph -> R e. U )
  assume fcobij.3: |- ( ph -> S e. V )
  assume fcobij.4: |- ( ph -> T e. W )
  assume fcobijfs.5: |- ( ph -> O e. S )
  assume fcobijfs.6: |- Q = ( G ` O )
  assume fcobijfs.7: |- X = { g e. ( S ^m R ) | g finSupp O }
  assume fcobijfs.8: |- Y = { h e. ( T ^m R ) | h finSupp Q }

  disjoint f h
  disjoint G f
  disjoint G h
  disjoint R f
  disjoint R h
  disjoint S f
  disjoint S h
  disjoint T f
  disjoint T h
  disjoint f ph
  disjoint h ph
  disjoint O f
  disjoint O h
  disjoint Q f
  disjoint Q h
  disjoint g h
  disjoint O g
  disjoint R g
  disjoint S g
  disjoint X f
  disjoint Y f
  assert |- ( ph -> ( f e. X |-> ( G o. f ) ) : X -1-1-onto-> Y )

  proof
    wph
    cX
    cY
    vf
    cX
    cG
    vf
    cv
    #
    cid
    cR
    cres
    #
    ccom
    ccom
    #
    cmpt
    #
    wf1o
    #
    cX
    cY
    vf
    cX
    cG
    @0
    ccom
    #
    cmpt
    #
    wf1o
    #
    wph
    vh
    cR
    cS
    cR
    cT
    cX
    cY
    vf
    @1
    cG
    cQ
    cO
    cX
    vg
    cv
    #
    cO
    cfsupp
    wbr
    #
    vg
    cS
    cR
    cmap
    co
    #
    crab
    #
    vh
    cv
    #
    cO
    cfsupp
    wbr
    #
    vh
    @10
    crab
    fcobijfs.7
    @13
    @9
    vh
    vg
    @10
    @12
    @8
    cO
    cfsupp
    breq1
    cbvrabv
    eqtr4i
    fcobijfs.8
    fcobijfs.6
    cR
    cR
    @1
    wf1o
    wph
    cR
    f1oi
    a1i
    fcobij.1
    wph
    cR
    cU
    wcel
    cR
    cvv
    wcel
    fcobij.2
    cR
    cU
    elex
    syl
    #
    wph
    cS
    cV
    wcel
    cS
    cvv
    wcel
    fcobij.3
    cS
    cV
    elex
    syl
    @14
    wph
    cT
    cW
    wcel
    cT
    cvv
    wcel
    fcobij.4
    cT
    cW
    elex
    syl
    fcobijfs.5
    mapfien
    wph
    @3
    @6
    wceq
    @4
    @7
    wb
    wph
    vf
    cX
    @2
    @5
    @0
    cX
    wcel
    wph
    @0
    @10
    wcel
    #
    @2
    @5
    wceq
    cX
    @10
    @0
    cX
    @11
    @10
    fcobijfs.7
    @9
    vg
    @10
    ssrab2
    eqsstri
    sseli
    wph
    @15
    wa
    #
    @2
    @5
    @1
    ccom
    #
    @5
    cG
    @0
    @1
    coass
    @16
    cR
    cT
    @5
    wf
    #
    @17
    @5
    wceq
    wph
    cS
    cT
    cG
    wf
    #
    cR
    cS
    @0
    wf
    @18
    @15
    wph
    cS
    cT
    cG
    wf1o
    @19
    fcobij.1
    cS
    cT
    cG
    f1of
    syl
    @0
    cS
    cR
    elmapi
    cR
    cS
    cT
    cG
    @0
    fco
    syl2an
    cR
    cT
    @5
    fcoi1
    syl
    syl5eqr
    sylan2
    mpteq2dva
    cX
    cY
    @3
    @6
    f1oeq1
    syl
    mpbid
end
