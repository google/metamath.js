include "wceq.mm"
include "wa.mm"
include "csn.mm"
include "cfv.mm"
include "adantr.mm"
include "clmod.mm"
include "wcel.mm"
include "wb.mm"
include "lspsneq0.mm"
include "syl2anc.mm"
include "biimpar.mm"
include "eqtr3d.mm"
include "mpbid.mm"
include "eqtrd.mm"
include "impbida.mm"

theorem lspsneq0b
  let wph: wff ph
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume lspsneq0b.v: |- V = ( Base ` W )
  assume lspsneq0b.o: |- .0. = ( 0g ` W )
  assume lspsneq0b.n: |- N = ( LSpan ` W )
  assume lspsneq0b.w: |- ( ph -> W e. LMod )
  assume lspsneq0b.x: |- ( ph -> X e. V )
  assume lspsneq0b.y: |- ( ph -> Y e. V )
  assume lspsneq0b.e: |- ( ph -> ( N ` { X } ) = ( N ` { Y } ) )


  assert |- ( ph -> ( X = .0. <-> Y = .0. ) )

  proof
    wph
    cX
    c.0
    wceq
    #
    cY
    c.0
    wceq
    #
    wph
    @0
    wa
    #
    cY
    csn
    cN
    cfv
    #
    c.0
    csn
    #
    wceq
    #
    @1
    @2
    cX
    csn
    cN
    cfv
    #
    @3
    @4
    wph
    @6
    @3
    wceq
    #
    @0
    lspsneq0b.e
    adantr
    wph
    @6
    @4
    wceq
    #
    @0
    wph
    cW
    clmod
    wcel
    #
    cX
    cV
    wcel
    @8
    @0
    wb
    #
    lspsneq0b.w
    lspsneq0b.x
    cN
    cV
    cW
    cX
    c.0
    lspsneq0b.v
    lspsneq0b.o
    lspsneq0b.n
    lspsneq0
    syl2anc
    #
    biimpar
    eqtr3d
    wph
    @5
    @1
    wb
    #
    @0
    wph
    @9
    cY
    cV
    wcel
    @12
    lspsneq0b.w
    lspsneq0b.y
    cN
    cV
    cW
    cY
    c.0
    lspsneq0b.v
    lspsneq0b.o
    lspsneq0b.n
    lspsneq0
    syl2anc
    #
    adantr
    mpbid
    wph
    @1
    wa
    #
    @8
    @0
    @14
    @6
    @3
    @4
    wph
    @7
    @1
    lspsneq0b.e
    adantr
    wph
    @5
    @1
    @13
    biimpar
    eqtrd
    wph
    @10
    @1
    @11
    adantr
    mpbid
    impbida
end
