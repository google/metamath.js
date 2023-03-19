include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wceq.mm"
include "wcel.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "cle.mm"
include "cxr.mm"
include "csupp.mm"
include "co.mm"
include "cima.mm"
include "csup.mm"
include "mdegval.mm"
include "syl.mm"
include "wss.mm"
include "crn.mm"
include "imassrn.mm"
include "cn0.mm"
include "cvv.mm"
include "wf.mm"
include "mplrcl.mm"
include "tdeglem1.mm"
include "frn.mm"
include "4syl.mm"
include "cr.mm"
include "nn0ssre.mm"
include "ressxr.mm"
include "sstri.mm"
include "syl6ss.mm"
include "syl5ss.mm"
include "supxrcl.mm"
include "eqeltrd.mm"
include "xrleid.mm"
include "wb.mm"
include "mdegleb.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "fveq2.mm"
include "breq2d.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "mpd.mm"

theorem mdeglt
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let vh: setvar h
  let vm: setvar m
  let cF: class F
  let cH: class H
  let cI: class I
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  let vf: setvar f
  let vi: setvar i
  let vr: setvar r
  let vy: setvar y
  let cG: class G
  assume mdegval.d: |- D = ( I mDeg R )
  assume mdegval.p: |- P = ( I mPoly R )
  assume mdegval.b: |- B = ( Base ` P )
  assume mdegval.z: |- .0. = ( 0g ` R )
  assume mdegval.a: |- A = { m e. ( NN0 ^m I ) | ( `' m " NN ) e. Fin }
  assume mdegval.h: |- H = ( h e. A |-> ( CCfld gsum h ) )
  assume mdeglt.f: |- ( ph -> F e. B )
  assume medglt.x: |- ( ph -> X e. A )
  assume mdeglt.lt: |- ( ph -> ( D ` F ) < ( H ` X ) )

  disjoint A h
  disjoint I m
  disjoint .0. h
  disjoint I h
  disjoint h m
  disjoint D x
  disjoint X x
  disjoint B f
  disjoint B i
  disjoint B r
  disjoint f i
  disjoint f r
  disjoint i r
  disjoint I f
  disjoint I i
  disjoint I r
  disjoint R f
  disjoint R i
  disjoint R r
  disjoint .0. i
  disjoint .0. r
  disjoint h i
  disjoint h r
  disjoint f h
  disjoint F f
  disjoint H f
  disjoint .0. f
  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint H x
  disjoint H y
  disjoint R x
  disjoint .0. x
  disjoint .0. y
  assert |- ( ph -> ( F ` X ) = .0. )

  proof
    wph
    cF
    cD
    cfv
    #
    cX
    cH
    cfv
    #
    clt
    wbr
    #
    cX
    cF
    cfv
    #
    c.0
    wceq
    #
    mdeglt.lt
    wph
    cX
    cA
    wcel
    @0
    vx
    cv
    #
    cH
    cfv
    #
    clt
    wbr
    #
    @5
    cF
    cfv
    #
    c.0
    wceq
    #
    wi
    #
    vx
    cA
    wral
    #
    @2
    @4
    wi
    #
    medglt.x
    wph
    @0
    @0
    cle
    wbr
    #
    @11
    wph
    @0
    cxr
    wcel
    #
    @13
    wph
    @0
    cH
    cF
    c.0
    csupp
    co
    #
    cima
    #
    cxr
    clt
    csup
    #
    cxr
    wph
    cF
    cB
    wcel
    #
    @0
    @17
    wceq
    mdeglt.f
    cA
    cB
    cD
    cP
    cR
    vh
    vm
    cF
    cH
    cI
    c.0
    mdegval.d
    mdegval.p
    mdegval.b
    mdegval.z
    mdegval.a
    mdegval.h
    mdegval
    syl
    wph
    @16
    cxr
    wss
    @17
    cxr
    wcel
    wph
    @16
    cH
    crn
    #
    cxr
    cH
    @15
    imassrn
    wph
    @19
    cn0
    cxr
    wph
    @18
    cI
    cvv
    wcel
    cA
    cn0
    cH
    wf
    @19
    cn0
    wss
    mdeglt.f
    cB
    cP
    cR
    cI
    cF
    mdegval.p
    mdegval.b
    mplrcl
    cA
    vh
    vm
    cH
    cI
    cvv
    mdegval.a
    mdegval.h
    tdeglem1
    cA
    cn0
    cH
    frn
    4syl
    cn0
    cr
    cxr
    nn0ssre
    ressxr
    sstri
    syl6ss
    syl5ss
    @16
    supxrcl
    syl
    eqeltrd
    #
    @0
    xrleid
    syl
    wph
    @18
    @14
    @13
    @11
    wb
    mdeglt.f
    @20
    vx
    cA
    cB
    cD
    cP
    cR
    vh
    vm
    cF
    @0
    cH
    cI
    c.0
    mdegval.d
    mdegval.p
    mdegval.b
    mdegval.z
    mdegval.a
    mdegval.h
    mdegleb
    syl2anc
    mpbid
    @10
    @12
    vx
    cX
    cA
    @5
    cX
    wceq
    #
    @7
    @2
    @9
    @4
    @21
    @6
    @1
    @0
    clt
    @5
    cX
    cH
    fveq2
    breq2d
    @21
    @8
    @3
    c.0
    @5
    cX
    cF
    fveq2
    eqeq1d
    imbi12d
    rspcva
    syl2anc
    mpd
end
