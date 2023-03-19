include "cfv.mm"
include "wceq.mm"
include "wne.mm"
include "wa.mm"
include "fveq2.mm"
include "adantl.mm"
include "crg.mm"
include "wcel.mm"
include "adantr.mm"
include "cn0.mm"
include "wi.mm"
include "eleq1a.mm"
include "syl.mm"
include "imp.mm"
include "wb.mm"
include "deg1nn0clb.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "deg1ldg.mm"
include "syl3anc.mm"
include "eqnetrrd.mm"
include "ex.mm"
include "necon2d.mm"
include "mpd.mm"

theorem deg1ldgn
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cF: class F
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vb: setvar b
  let vd: setvar d
  let va: setvar a
  let vc: setvar c
  assume deg1z.d: |- D = ( deg1 ` R )
  assume deg1z.p: |- P = ( Poly1 ` R )
  assume deg1z.z: |- .0. = ( 0g ` P )
  assume deg1nn0cl.b: |- B = ( Base ` P )
  assume deg1ldg.y: |- Y = ( 0g ` R )
  assume deg1ldg.a: |- A = ( coe1 ` F )
  assume deg1ldgn.r: |- ( ph -> R e. Ring )
  assume deg1ldgn.f: |- ( ph -> F e. B )
  assume deg1ldgn.x: |- ( ph -> X e. NN0 )
  assume deg1ldgn.e: |- ( ph -> ( A ` X ) = Y )


  assert |- ( ph -> ( D ` F ) =/= X )

  proof
    wph
    cX
    cA
    cfv
    #
    cY
    wceq
    cF
    cD
    cfv
    #
    cX
    wne
    deg1ldgn.e
    wph
    @1
    cX
    @0
    cY
    wph
    @1
    cX
    wceq
    #
    @0
    cY
    wne
    wph
    @2
    wa
    #
    @1
    cA
    cfv
    #
    @0
    cY
    @2
    @4
    @0
    wceq
    wph
    @1
    cX
    cA
    fveq2
    adantl
    @3
    cR
    crg
    wcel
    #
    cF
    cB
    wcel
    #
    cF
    c.0
    wne
    #
    @4
    cY
    wne
    wph
    @5
    @2
    deg1ldgn.r
    adantr
    wph
    @6
    @2
    deg1ldgn.f
    adantr
    @3
    @7
    @1
    cn0
    wcel
    #
    wph
    @2
    @8
    wph
    cX
    cn0
    wcel
    @2
    @8
    wi
    deg1ldgn.x
    cX
    cn0
    @1
    eleq1a
    syl
    imp
    wph
    @7
    @8
    wb
    #
    @2
    wph
    @5
    @6
    @9
    deg1ldgn.r
    deg1ldgn.f
    cB
    cD
    cP
    cR
    cF
    c.0
    deg1z.d
    deg1z.p
    deg1z.z
    deg1nn0cl.b
    deg1nn0clb
    syl2anc
    adantr
    mpbird
    cA
    cB
    cD
    cP
    cR
    cF
    cY
    c.0
    deg1z.d
    deg1z.p
    deg1z.z
    deg1nn0cl.b
    deg1ldg.y
    deg1ldg.a
    deg1ldg
    syl3anc
    eqnetrrd
    ex
    necon2d
    mpd
end
