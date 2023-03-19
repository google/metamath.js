include "csn.mm"
include "cfv.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "clmod.mm"
include "adantr.mm"
include "simpr.mm"
include "lsatn0.mm"
include "wceq.mm"
include "sneq.mm"
include "fveq2d.mm"
include "adantl.mm"
include "lspsn0.mm"
include "syl.mm"
include "eqtrd.mm"
include "ex.mm"
include "necon3d.mm"
include "mpd.mm"
include "cdif.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "lsatlspsn.mm"
include "impbida.mm"

theorem lsatspn0
  let wph: wff ph
  let cA: class A
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume lsatspn0.v: |- V = ( Base ` W )
  assume lsatspn0.n: |- N = ( LSpan ` W )
  assume lsatspn0.o: |- .0. = ( 0g ` W )
  assume lsatspn0.a: |- A = ( LSAtoms ` W )
  assume isateln0.w: |- ( ph -> W e. LMod )
  assume isateln0.x: |- ( ph -> X e. V )


  assert |- ( ph -> ( ( N ` { X } ) e. A <-> X =/= .0. ) )

  proof
    wph
    cX
    csn
    #
    cN
    cfv
    #
    cA
    wcel
    #
    cX
    c.0
    wne
    #
    wph
    @2
    wa
    #
    @1
    c.0
    csn
    #
    wne
    @3
    @4
    cA
    @1
    cW
    c.0
    lsatspn0.o
    lsatspn0.a
    wph
    cW
    clmod
    wcel
    #
    @2
    isateln0.w
    adantr
    #
    wph
    @2
    simpr
    lsatn0
    @4
    cX
    c.0
    @1
    @5
    @4
    cX
    c.0
    wceq
    #
    @1
    @5
    wceq
    @4
    @8
    wa
    #
    @1
    @5
    cN
    cfv
    #
    @5
    @8
    @1
    @10
    wceq
    @4
    @8
    @0
    @5
    cN
    cX
    c.0
    sneq
    fveq2d
    adantl
    @9
    @6
    @10
    @5
    wceq
    @4
    @6
    @8
    @7
    adantr
    cN
    cW
    c.0
    lsatspn0.o
    lsatspn0.n
    lspsn0
    syl
    eqtrd
    ex
    necon3d
    mpd
    wph
    @3
    wa
    #
    cA
    cN
    cV
    cW
    cX
    c.0
    lsatspn0.v
    lsatspn0.n
    lsatspn0.o
    lsatspn0.a
    wph
    @6
    @3
    isateln0.w
    adantr
    @11
    cX
    cV
    wcel
    #
    @3
    cX
    cV
    @5
    cdif
    wcel
    wph
    @12
    @3
    isateln0.x
    adantr
    wph
    @3
    simpr
    cX
    cV
    c.0
    eldifsn
    sylanbrc
    lsatlspsn
    impbida
end
