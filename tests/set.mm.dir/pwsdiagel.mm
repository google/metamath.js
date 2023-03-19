include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cxp.mm"
include "wf.mm"
include "fconst6g.mm"
include "adantl.mm"
include "wb.mm"
include "pwselbasb.mm"
include "adantr.mm"
include "mpbird.mm"

theorem pwsdiagel
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  assume pwsdiagel.y: |- Y = ( R ^s I )
  assume pwsdiagel.b: |- B = ( Base ` R )
  assume pwsdiagel.c: |- C = ( Base ` Y )


  assert |- ( ( ( R e. V /\ I e. W ) /\ A e. B ) -> ( I X. { A } ) e. C )

  proof
    cR
    cV
    wcel
    cI
    cW
    wcel
    wa
    #
    cA
    cB
    wcel
    #
    wa
    cI
    cA
    csn
    cxp
    #
    cC
    wcel
    #
    cI
    cB
    @2
    wf
    #
    @1
    @4
    @0
    cI
    cA
    cB
    fconst6g
    adantl
    @0
    @3
    @4
    wb
    @1
    cB
    cR
    cI
    cC
    cV
    @2
    cY
    cW
    pwsdiagel.y
    pwsdiagel.b
    pwsdiagel.c
    pwselbasb
    adantr
    mpbird
end
