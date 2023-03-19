include "cn0.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "ccnv.mm"
include "cfv.mm"
include "cle.mm"
include "wb.mm"
include "znleval.mm"
include "3ad2ant1.mm"
include "wa.mm"
include "3simpc.mm"
include "biantrurd.mm"
include "df-3an.mm"
include "syl6bbr.mm"
include "bitr4d.mm"

theorem znleval2
  let cA: class A
  let cB: class B
  let cF: class F
  let c.le: class .<_
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume znle2.y: |- Y = ( Z/nZ ` N )
  assume znle2.f: |- F = ( ( ZRHom ` Y ) |` W )
  assume znle2.w: |- W = if ( N = 0 , ZZ , ( 0 ..^ N ) )
  assume znle2.l: |- .<_ = ( le ` Y )
  assume znleval.x: |- X = ( Base ` Y )


  assert |- ( ( N e. NN0 /\ A e. X /\ B e. X ) -> ( A .<_ B <-> ( `' F ` A ) <_ ( `' F ` B ) ) )

  proof
    cN
    cn0
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cA
    cB
    c.le
    wbr
    #
    @1
    @2
    cA
    cF
    ccnv
    #
    cfv
    cB
    @5
    cfv
    cle
    wbr
    #
    w3a
    #
    @6
    @0
    @1
    @4
    @7
    wb
    @2
    cA
    cB
    cF
    c.le
    cN
    cW
    cX
    cY
    znle2.y
    znle2.f
    znle2.w
    znle2.l
    znleval.x
    znleval
    3ad2ant1
    @3
    @6
    @1
    @2
    wa
    #
    @6
    wa
    @7
    @3
    @8
    @6
    @0
    @1
    @2
    3simpc
    biantrurd
    @1
    @2
    @6
    df-3an
    syl6bbr
    bitr4d
end
