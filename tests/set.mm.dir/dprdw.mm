include "cv.mm"
include "cfv.mm"
include "cixp.mm"
include "wcel.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wa.mm"
include "wfn.mm"
include "wral.mm"
include "w3a.mm"
include "cvv.mm"
include "wi.mm"
include "elex.mm"
include "a1i.mm"
include "dprddomcld.mm"
include "fnex.mm"
include "expcom.mm"
include "syl.mm"
include "adantrd.mm"
include "wb.mm"
include "fveq2.mm"
include "cbvixpv.mm"
include "eleq2i.mm"
include "elixp2.mm"
include "3anass.mm"
include "3bitri.mm"
include "baib.mm"
include "pm5.21ndd.mm"
include "anbi1d.mm"
include "breq1.mm"
include "elrab2.mm"
include "df-3an.mm"
include "3bitr4g.mm"

theorem dprdw
  let wph: wff ph
  let vx: setvar x
  let cS: class S
  let vh: setvar h
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cI: class I
  let cW: class W
  let c.0: class .0.
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cX: class X
  let cZ: class Z
  assume dprdff.w: |- W = { h e. X_ i e. I ( S ` i ) | h finSupp .0. }
  assume dprdff.1: |- ( ph -> G dom DProd S )
  assume dprdff.2: |- ( ph -> dom S = I )

  disjoint h x
  disjoint F h
  disjoint F x
  disjoint G x
  disjoint h i
  disjoint I h
  disjoint i x
  disjoint I i
  disjoint I x
  disjoint .0. h
  disjoint ph x
  disjoint S h
  disjoint S i
  disjoint S x
  disjoint h y
  disjoint h z
  disjoint A h
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint x y
  disjoint x z
  disjoint F y
  disjoint F z
  disjoint G y
  disjoint G z
  disjoint i y
  disjoint i z
  disjoint I y
  disjoint I z
  disjoint ph y
  disjoint ph z
  disjoint S y
  disjoint S z
  disjoint X x
  disjoint Z y
  assert |- ( ph -> ( F e. W <-> ( F Fn I /\ A. x e. I ( F ` x ) e. ( S ` x ) /\ F finSupp .0. ) ) )

  proof
    wph
    cF
    vi
    cI
    vi
    cv
    #
    cS
    cfv
    #
    cixp
    #
    wcel
    #
    cF
    c.0
    cfsupp
    wbr
    #
    wa
    cF
    cI
    wfn
    #
    vx
    cv
    #
    cF
    cfv
    @6
    cS
    cfv
    #
    wcel
    vx
    cI
    wral
    #
    wa
    #
    @4
    wa
    cF
    cW
    wcel
    @5
    @8
    @4
    w3a
    wph
    @3
    @9
    @4
    wph
    cF
    cvv
    wcel
    #
    @3
    @9
    @3
    @10
    wi
    wph
    cF
    @2
    elex
    a1i
    wph
    @5
    @10
    @8
    wph
    cI
    cvv
    wcel
    #
    @5
    @10
    wi
    wph
    cS
    cG
    cI
    dprdff.1
    dprdff.2
    dprddomcld
    @5
    @11
    @10
    cI
    cvv
    cF
    fnex
    expcom
    syl
    adantrd
    @10
    @3
    @9
    wb
    wi
    wph
    @3
    @10
    @9
    @3
    cF
    vx
    cI
    @7
    cixp
    #
    wcel
    @10
    @5
    @8
    w3a
    @10
    @9
    wa
    @2
    @12
    cF
    vi
    vx
    cI
    @1
    @7
    @0
    @6
    cS
    fveq2
    cbvixpv
    eleq2i
    vx
    cI
    @7
    cF
    elixp2
    @10
    @5
    @8
    3anass
    3bitri
    baib
    a1i
    pm5.21ndd
    anbi1d
    vh
    cv
    #
    c.0
    cfsupp
    wbr
    @4
    vh
    cF
    @2
    cW
    @13
    cF
    c.0
    cfsupp
    breq1
    dprdff.w
    elrab2
    @5
    @8
    @4
    df-3an
    3bitr4g
end
